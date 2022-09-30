// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::async_runtime as rt;
use crate::db::models as m;
use crate::db::{ConnectionPool, DeferredTxConnection};
use crate::encryption::Keychain;
use crate::protocols::eth;
use crate::public_suffix_list::PublicSuffixList;
use crate::{assets, config, Error};
use jsonrpsee::core::server::helpers::MethodResponse;
use jsonrpsee::types::error::{CallError, ErrorCode};
use jsonrpsee::types::{ErrorObject, Params, Request};
use lazy_static::lazy_static;
use num_traits::{FromPrimitive, ToPrimitive};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fmt::Debug;
use std::iter;
use std::str::FromStr;
use strum_macros::{EnumIter, EnumString};
use typed_builder::TypedBuilder;
use url::Url;
use crate::favicon::fetch_favicons;
use crate::http_client::HttpClient;

#[derive(Debug)]
#[readonly::make]
pub(super) struct InPageProvider<'a> {
    keychain: &'a Keychain,
    connection_pool: &'a ConnectionPool,
    public_suffix_list: &'a PublicSuffixList,
    rpc_manager: &'a dyn eth::RpcManagerI,
    http_client: &'a HttpClient,
    request_context: Box<dyn InPageRequestContextI>,
    url: Url,
}

impl<'a> InPageProvider<'a> {
    pub(super) fn new(
        keychain: &'a Keychain,
        connection_pool: &'a ConnectionPool,
        public_suffix_list: &'a PublicSuffixList,
        rpc_manager: &'a dyn eth::RpcManagerI,
        http_client: &'a HttpClient,
        request_context: Box<dyn InPageRequestContextI>,
    ) -> Result<Self, Error> {
        let url = Url::parse(&request_context.page_url())?;
        Ok(Self {
            keychain,
            connection_pool,
            public_suffix_list,
            rpc_manager,
            http_client,
            request_context,
            url,
        })
    }

    // TODO add rate limiting
    // TODO refuse in page requests if dapp wasn't served over https or doesn't have a registrable
    // domain unless in dev mode.
    pub(super) fn in_page_request(&self, raw_request: &str) -> Result<String, Error> {
        let response = self.raw_json_rpc_request(raw_request)?;
        // Prevent reflected XSS by passing the result as hexadecimal utf-8 bytes to JS.
        // See the security model in the developer docs for more.
        Ok(hex::encode(response.result.as_bytes()))
    }

    fn raw_json_rpc_request(&self, raw_request: &str) -> Result<MethodResponse, Error> {
        // We can only return JSON RPC message with error if we can parse the message,
        // because we need the request id for that, hence the `CoreError` here.
        if raw_request.as_bytes().len() > config::MAX_JSONRPC_REQUEST_SIZE_BYTES {
            return Err(invalid_raw_request());
        }
        let req: Request =
            serde_json::from_str(raw_request).map_err(|_| invalid_raw_request())?;
        match self.dispatch(&req) {
            Ok(result) => Ok(MethodResponse::response(
                req.id,
                result,
                config::MAX_JSONRPC_RESPONSE_SIZE_BYTES,
            )),
            Err(Error::JsonRpc { code, message }) => {
                // We need to select a data type even though data is none, <String>
                let data: Option<String> = None;
                let error_object = ErrorObject::owned(code.code(), message, data);
                Ok(MethodResponse::error(req.id, error_object))
            }
            Err(error) => Err(error),
        }
    }

    /// Resolve JSON-RPC method.
    fn dispatch(&self, request: &Request) -> Result<serde_json::Value, Error> {
        // Start the transaction here to make sure we see a consistent view of the DB during the
        // entire request handling.
        self.connection_pool.deferred_transaction(|mut tx_conn| {
            let maybe_address = self.fetch_address_for_approved_dapp(&mut tx_conn)?;
            match &*request.method {
                // These methods request the user approval if the user hasn't added the dapp yet
                // in the account.
                "eth_requestAccounts" | "eth_accounts" => {
                    self.eth_request_accounts(&mut tx_conn, maybe_address)
                }
                _ => match maybe_address {
                    Some(address) => {
                        self.dispatch_authorized_methods(request, &mut tx_conn, address)
                    }
                    None => {
                        let err: Error = InPageErrorCode::Unauthorized.into();
                        Err(err)
                    }
                },
            }
        })
    }

    /// Resolve JSON-RPC method if user has approved the dapp in the current account.
    fn dispatch_authorized_methods(
        &self,
        request: &Request,
        tx_conn: &mut DeferredTxConnection,
        address: m::Address,
    ) -> Result<serde_json::Value, Error> {
        let params = Params::new(request.params.map(|params| params.get()));
        match &*request.method {
            "eth_chainId" => self.eth_chain_id(tx_conn),
            "eth_sendTransaction" => {
                self.eth_send_transaction(request.params, tx_conn, address)
            }
            "personal_sign" => self.personal_sign(request.params, tx_conn, address),
            "wallet_addEthereumChain" => self.wallet_add_ethereum_chain(params),
            "wallet_switchEthereumChain" => {
                self.wallet_switch_ethereum_chain(params, tx_conn, address)
            }
            "web3_clientVersion" => self.web3_client_version(),
            "web3_sha3" => self.web3_sha3(request.params),
            method => self.proxy_method(tx_conn, method, request.params),
        }
    }

    /// Notify the in-page JS about an event in the background.
    fn notify(&self, message: &ProviderMessage) -> Result<(), Error> {
        let json_message = serde_json::to_string(&message).map_err(|_| Error::Fatal {
            error: format!(
                "Failed to deserialize message for event: '{:?}'",
                message.event
            ),
        })?;
        let message_hex = hex::encode(json_message);
        let callbacks = self.request_context.callbacks();
        // TODO notification should happen on a background thread as the processing may be blocking,
        // but doing that crashes in iOS UI tests (not when manually testing the simulator though).
        callbacks.notify(message_hex);
        Ok(())
    }

    fn notify_connect(
        &self,
        chain_id: eth::ChainId,
        selected_address: &str,
    ) -> Result<(), Error> {
        let network_version = chain_id.network_version();
        let event = SealVaultConnect {
            chain_id: chain_id.into(),
            network_version: &network_version,
            selected_address,
        };
        let data = serde_json::to_value(&event).map_err(|_| Error::Fatal {
            error: format!("Failed to deserialize SealVaultConnect event: {:?}", event),
        })?;
        let message = ProviderMessage {
            event: ProviderEvent::SealVaultConnect,
            data,
        };
        self.notify(&message)
    }

    fn notify_chain_changed(&self, chain_id: eth::ChainId) -> Result<(), Error> {
        let chain_id_json = chain_id_to_hex_str_json(chain_id)?;
        let chain_message = ProviderMessage {
            event: ProviderEvent::ChainChanged,
            data: chain_id_json,
        };
        self.notify(&chain_message)?;

        let network_version = chain_id.network_version();
        let network_version =
            serde_json::to_value(&network_version).map_err(|err| Error::Fatal {
                error: err.to_string(),
            })?;
        let network_message = ProviderMessage {
            event: ProviderEvent::NetworkChanged,
            data: network_version,
        };
        self.notify(&network_message)
    }

    fn proxy_method<T>(
        &self,
        tx_conn: &mut DeferredTxConnection,
        method: &str,
        params: T,
    ) -> Result<serde_json::Value, Error>
    where
        T: Debug + Serialize + Send + Sync,
    {
        if !PROXIED_RPC_METHODS.contains(method) {
            // Must return 4200 for unsupported method for Ethereum
            // https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1193.md#supported-rpc-methods
            return Err(Error::JsonRpc {
                code: InPageErrorCode::UnsupportedMethod.into(),
                message: format!("This method is not supported: '{}'", method),
            });
        }

        let rpc_provider = self.chain_rpc_provider(tx_conn)?;
        rpc_provider.proxy_rpc_request(method, params)
    }

    fn eth_chain_id(
        &self,
        tx_conn: &mut DeferredTxConnection,
    ) -> Result<serde_json::Value, Error> {
        let chain_id = self.fetch_eth_chain_id(tx_conn)?;

        let chain_id: ethers::core::types::U64 = chain_id.into();
        let result = to_value(chain_id)?;
        Ok(result)
    }

    fn chain_rpc_provider(
        &self,
        tx_conn: &mut DeferredTxConnection,
    ) -> Result<eth::RpcProvider, Error> {
        let chain_id = self.fetch_eth_chain_id(tx_conn)?;
        let provider = self.rpc_manager.eth_api_provider(chain_id);
        Ok(provider)
    }

    fn fetch_eth_chain_id(
        &self,
        tx_conn: &mut DeferredTxConnection,
    ) -> Result<eth::ChainId, Error> {
        let account_id = m::LocalSettings::fetch_active_account_id(tx_conn.as_mut())?;
        let dapp_id = m::Dapp::fetch_id_for_account(
            tx_conn.as_mut(),
            self.url.clone(),
            self.public_suffix_list,
            &account_id,
        )?;
        // Dapp has not been approved in the current account.
        let dapp_id = dapp_id.ok_or_else(|| {
            let error: Error = InPageErrorCode::Unauthorized.into();
            error
        })?;
        let params = m::DappSessionParams::builder()
            .dapp_id(&dapp_id)
            .account_id(&account_id)
            .build();
        let chain_id =
            m::LocalDappSession::fetch_eth_chain_id(tx_conn.as_mut(), &params)?;
        Ok(chain_id)
    }

    fn eth_request_accounts(
        &self,
        tx_conn: &mut DeferredTxConnection,
        maybe_address: Option<m::Address>,
    ) -> Result<serde_json::Value, Error> {
        let selected_address = match maybe_address {
            // User has approved the dapp before in this account.
            Some(address) => Ok(address.address),
            // Request permission from user to add the dapp to the account.
            None => {
                let account_id =
                    m::LocalSettings::fetch_active_account_id(tx_conn.as_mut())?;
                let address = self.request_add_new_dapp(tx_conn, &account_id)?;
                match address {
                    // User approved, return the newly created address.
                    Some(address) => Ok(address),
                    // User declined, return JSON-RPC error.
                    None => {
                        let err: Error = InPageErrorCode::UserRejected.into();
                        Err(err)
                    }
                }
            }
        }?;

        let chain_id = self.fetch_eth_chain_id(tx_conn)?;
        self.notify_connect(chain_id, &selected_address)?;

        let result = to_value(vec![selected_address])?;
        Ok(result)
    }

    fn fetch_address_for_approved_dapp(
        &self,
        tx_conn: &mut DeferredTxConnection,
    ) -> Result<Option<m::Address>, Error> {
        let account_id = m::LocalSettings::fetch_active_account_id(tx_conn.as_mut())?;
        let maybe_dapp_id = m::Dapp::fetch_id_for_account(
            tx_conn.as_mut(),
            self.url.clone(),
            self.public_suffix_list,
            &account_id,
        )?;
        let maybe_address: Option<m::Address> = match maybe_dapp_id {
            Some(dapp_id) => {
                let params = m::DappSessionParams::builder()
                    .dapp_id(&dapp_id)
                    .account_id(&account_id)
                    .build();
                let address = m::LocalDappSession::create_eth_session_if_not_exists(
                    tx_conn, &params,
                )?;
                Some(address)
            }
            None => None,
        };
        Ok(maybe_address)
    }

    /// Add a new dapp to the account requesting the user's approval and return the new 1DK address
    /// if the user approved it.
    fn request_add_new_dapp(
        &self,
        tx_conn: &mut DeferredTxConnection,
        account_id: &str,
    ) -> Result<Option<String>, Error> {
        let dapp_identifier =
            m::Dapp::dapp_identifier(self.url.clone(), self.public_suffix_list)?;
        let favicon = self.fetch_favicon()?;
        let dapp_approval = DappApprovalParams::builder()
            .account_id(account_id.to_string())
            .dapp_identifier(dapp_identifier)
            .favicon(favicon)
            .build();
        let callbacks = self.request_context.callbacks();
        let user_approved = callbacks.approve_dapp(dapp_approval);
        if user_approved {
            let address = self.add_new_dapp(tx_conn, account_id)?;
            Ok(Some(address))
        } else {
            Ok(None)
        }
    }

    fn fetch_favicon(
        &self,
    ) -> Result<Option<Vec<u8>>, Error> {
        let favicons = fetch_favicons(self.http_client, iter::once(self.url.clone()))?;
        let favicon = favicons.into_iter().next().flatten();
        Ok(favicon)
    }


    /// Add a new dapp to the account and return the dapp's deterministic id.
    /// Also transfers the configured default amount to the new dapp address.
    fn add_new_dapp(
        &self,
        tx_conn: &mut DeferredTxConnection,
        account_id: &str,
    ) -> Result<String, Error> {
        // Add dapp to account and create local session
        let chain_id = eth::ChainId::default_dapp_chain();
        let dapp_id = self.add_eth_dapp_to_account(tx_conn, account_id, chain_id)?;
        let params = m::DappSessionParams::builder()
            .dapp_id(&dapp_id)
            .account_id(account_id)
            .chain_id(Some(chain_id))
            .build();
        let address = m::LocalDappSession::create_eth_session(tx_conn, &params)?;
        let address_return = address.address.clone();

        // Transfer default dapp allotment to new dapp address from account wallet.
        let wallet_address_id =
            m::Address::fetch_eth_wallet_id(tx_conn, account_id, chain_id)?;
        let chain_setings =
            m::Chain::fetch_user_settings_for_eth_chain(tx_conn.as_mut(), chain_id)?;
        let provider = self.rpc_manager.eth_api_provider(chain_id);
        let wallet_signing_key = m::Address::fetch_eth_signing_key(
            tx_conn,
            self.keychain,
            &wallet_address_id,
        )?;
        // Call blockchain API in background.
        rt::spawn_blocking(move || {
            // Call fails if there are insufficient funds.
            let res = provider.transfer_native_token(
                &wallet_signing_key,
                &address.address,
                &chain_setings.default_dapp_allotment,
            );
            match res {
                Ok(_) => (),
                Err(err) => {
                    // TODO display error message in ui instead
                    log::info!(
                        "Failed to transfer allotment to new dapp due to error: {}",
                        err
                    );
                }
            }
        });
        Ok(address_return)
    }

    fn add_eth_dapp_to_account(
        &self,
        tx_conn: &mut DeferredTxConnection,
        account_id: &str,
        chain_id: eth::ChainId,
    ) -> Result<String, Error> {
        let dapp_id = m::Dapp::create_if_not_exists(
            tx_conn,
            self.url.clone(),
            self.public_suffix_list,
        )?;
        m::Address::create_eth_key_and_address(
            tx_conn,
            self.keychain,
            account_id,
            chain_id,
            Some(&dapp_id),
            false,
        )?;
        Ok(dapp_id)
    }

    fn eth_send_transaction(
        &self,
        params: Option<&'a serde_json::value::RawValue>,
        tx_conn: &mut DeferredTxConnection,
        address: m::Address,
    ) -> Result<serde_json::Value, Error> {
        let signing_key = m::Address::fetch_eth_signing_key(
            tx_conn,
            self.keychain,
            &address.deterministic_id,
        )?;

        let params = Params::new(params.map(|params| params.get()));
        // TODO use EIP-1559 once we can get reliable max_priority_fee_per_gas estimates on all
        // chains.
        let mut tx: ethers::core::types::TransactionRequest =
            params.one().map_err(|_| {
                let err: Error = InPageErrorCode::InvalidParams.into();
                err
            })?;
        // Remove nonce to fill with latest nonce from remote API in signer to make sure tx nonce is
        // current. MetaMask does this too.
        tx.nonce = None;

        let provider = self.rpc_manager.eth_api_provider(signing_key.chain_id);
        let tx_hash = provider.send_transaction(&signing_key, tx)?;

        to_value(tx_hash)
    }

    fn personal_sign(
        &self,
        params: Option<&'a serde_json::value::RawValue>,
        tx_conn: &mut DeferredTxConnection,
        address: m::Address,
    ) -> Result<serde_json::Value, Error> {
        let params = Params::new(params.map(|params| params.get()));
        let mut params = params.sequence();
        let message: String = params.next()?;
        let message = decode_0x_hex_prefix(&message)?;
        let request_address: ethers::core::types::Address =
            ethers::core::types::Address::from_str(&address.address)
                .expect("address from database is valid");
        let address_arg: ethers::core::types::Address = params.next()?;
        if address_arg != request_address {
            return Err(Error::JsonRpc {
                code: InPageErrorCode::InvalidParams.into(),
                message: "Invalid address".into(),
            });
        }

        // Password argument is ignored.
        let _password: Option<String> = params.optional_next()?;

        let signing_key = m::Address::fetch_eth_signing_key(
            tx_conn,
            self.keychain,
            &address.deterministic_id,
        )?;
        let signer = eth::Signer::new(&signing_key);
        let signature = signer.personal_sign(message)?;

        to_value(signature.to_string())
    }

    /// We don't support adding chains that aren't supported already, so this is a noop if the chain
    /// is already supported and an error if it isn't.
    fn wallet_add_ethereum_chain(
        &self,
        params: Params,
    ) -> Result<serde_json::Value, Error> {
        let chain_params: AddEthereumChainParameter = params.sequence().next()?;
        // If we can parse it, it's a supported chain id which means it was "added".
        let _chain_id: eth::ChainId = parse_0x_chain_id(&chain_params.chain_id)?;
        // Result should be null on success. We need type annotations for serde.
        let result: Option<String> = None;
        to_value(result)
    }

    fn wallet_switch_ethereum_chain(
        &self,
        params: Params,
        tx_conn: &mut DeferredTxConnection,
        address: m::Address,
    ) -> Result<serde_json::Value, Error> {
        let chain_id: SwitchEthereumChainParameter = params.sequence().next()?;
        let chain_id: eth::ChainId = parse_0x_chain_id(&chain_id.chain_id)?;
        let chain_entity_id = m::Chain::fetch_or_create_eth_chain_id(tx_conn, chain_id)?;

        let address_entity = m::AddressEntity::builder()
            .asymmetric_key_id(&address.asymmetric_key_id)
            .chain_entity_id(&chain_entity_id)
            .build();
        let new_address_id =
            m::Address::fetch_or_create_for_eth_chain(tx_conn, &address_entity)?;
        let update_session_params = m::UpdateDappSessionParams::builder()
            .old_address_id(&address.deterministic_id)
            .new_address_id(&new_address_id)
            .build();
        m::LocalDappSession::update_session_address(tx_conn, &update_session_params)?;

        self.notify_chain_changed(chain_id)?;

        // Result should be null on success. We need type annotations for serde.
        let result: Option<String> = None;
        to_value(result)
    }

    fn web3_client_version(&self) -> Result<serde_json::Value, Error> {
        Ok("SealVault".into())
    }

    fn web3_sha3(
        &self,
        params: Option<&'a serde_json::value::RawValue>,
    ) -> Result<serde_json::Value, Error> {
        let params = Params::new(params.map(|params| params.get()));
        let mut params = params.sequence();
        let message: String = params.next()?;
        let message = decode_0x_hex_prefix(&message)?;
        let hash = ethers::core::utils::keccak256(message);
        let result = format!("0x{}", hex::encode(hash));
        to_value(result)
    }
}

pub trait InPageRequestContextI: Send + Sync + Debug {
    fn page_url(&self) -> String;
    fn callbacks(&self) -> Box<dyn CoreInPageCallbackI>;
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct DappApprovalParams {
    /// The account for which the dapp approval is set.
    #[builder(setter(into))]
    pub account_id: String,
    /// A human readable dapp identifier that can be presented to the user.
    #[builder(setter(into))]
    pub dapp_identifier: String,
    /// The dapps favicon
    #[builder(setter(into))]
    pub favicon: Option<Vec<u8>>,
}

pub trait CoreInPageCallbackI: Send + Sync + Debug {
    /// Request a dapp approval from the user through the UI.
    /// After the user has approved the dapp for the first time, it'll be allowed to connect and
    /// execute transactions automatically.
    fn approve_dapp(&self, dapp_approval: DappApprovalParams) -> bool;

    /// Notify the in-page provider of an event.
    fn notify(&self, event_hex: String);
}
// Implement for all targets, not only testing to let the dev server use it too.
#[derive(Debug)]
pub struct InPageRequestContextMock {
    pub page_url: String,
    pub callbacks: Box<CoreInPageCallbackMock>,
}

impl InPageRequestContextMock {
    pub fn new(page_url: &str) -> Self {
        Self {
            page_url: page_url.into(),
            callbacks: Box::new(CoreInPageCallbackMock::new()),
        }
    }
    pub fn default_boxed() -> Box<Self> {
        Box::new(InPageRequestContextMock::new("https://example.com"))
    }
}

impl InPageRequestContextI for InPageRequestContextMock {
    fn page_url(&self) -> String {
        self.page_url.clone()
    }

    fn callbacks(&self) -> Box<dyn CoreInPageCallbackI> {
        self.callbacks.clone()
    }
}

#[derive(Debug, Clone)]
pub struct CoreInPageCallbackMock {}

impl CoreInPageCallbackMock {
    // We don't want to create the mock by accident with `Default::default`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {}
    }
}

impl CoreInPageCallbackI for CoreInPageCallbackMock {
    fn approve_dapp(&self, _: DappApprovalParams) -> bool {
        // Don't slow down tests noticeably, but simulate blocking.
        std::thread::sleep(std::time::Duration::from_millis(1));
        true
    }

    fn notify(&self, event: String) {
        let event = hex::decode(event).expect("valid hex");
        let event = String::from_utf8_lossy(&event);
        log::info!("CoreInPageCallbackMock.notify: '{:?}'", event);
    }
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ProviderMessage {
    event: ProviderEvent,
    data: serde_json::Value,
}

// Custom EIP-1193 connect event as we need to send more data to the in-page script
// than what the standard permits. We trigger the standard `connect` event in the
// in-page script once this message is received.
// https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1193.md#connect
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct SealVaultConnect<'a> {
    chain_id: ethers::core::types::U64,
    network_version: &'a str,
    selected_address: &'a str,
}

#[derive(Debug, strum_macros::Display, EnumIter, EnumString, Serialize, Deserialize)]
#[strum(serialize_all = "camelCase")]
#[serde(rename_all = "camelCase")]
enum ProviderEvent {
    // https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1193.md#connect-1
    Connect,
    // https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1193.md#chainchanged
    ChainChanged,
    // https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1193.md#accountschanged
    AccountsChanged,
    // Legacy MetaMask https://docs.metamask.io/guide/ethereum-provider.html#legacy-events
    NetworkChanged,
    // Custom connect event as we need to inject the networkVersion in addition to chainId
    SealVaultConnect,
}

/// Incomplete because we only care about the chain_id param.
/// From https://docs.metamask.io/guide/rpc-api.html#wallet-addethereumchain
#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AddEthereumChainParameter {
    chain_id: String, // A 0x-prefixed hexadecimal string
}

/// From https://docs.metamask.io/guide/rpc-api.html#wallet-switchethereumchain
#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct SwitchEthereumChainParameter {
    chain_id: String, // A 0x-prefixed hexadecimal string
}

fn strip_0x_hex_prefix(s: &str) -> Result<&str, Error> {
    s.strip_prefix("0x").ok_or_else(|| Error::JsonRpc {
        code: InPageErrorCode::InvalidParams.into(),
        message: "Message must start with 0x".into(),
    })
}

fn decode_0x_hex_prefix(s: &str) -> Result<Vec<u8>, Error> {
    let s = strip_0x_hex_prefix(s)?;
    hex::decode(s).map_err(|_| Error::JsonRpc {
        code: InPageErrorCode::InvalidParams.into(),
        message: "Invalid hex".into(),
    })
}

fn parse_0x_chain_id(hex_chain_id: &str) -> Result<eth::ChainId, Error> {
    // U64 should support
    let chain_id = strip_0x_hex_prefix(hex_chain_id)?;
    let chain_id =
        ethers::core::types::U64::from_str_radix(chain_id, 16).map_err(|_| {
            Error::JsonRpc {
                code: InPageErrorCode::InvalidParams.into(),
                message: "Invalid U64".into(),
            }
        })?;
    let chain_id: eth::ChainId =
        FromPrimitive::from_u64(chain_id.as_u64()).ok_or_else(|| Error::JsonRpc {
            code: InPageErrorCode::InvalidParams.into(),
            message: "Unsupported chain id".into(),
        })?;
    Ok(chain_id)
}

fn chain_id_to_hex_str_json(chain_id: eth::ChainId) -> Result<serde_json::Value, Error> {
    let chain_id: ethers::core::types::U64 = chain_id.into();
    to_value(chain_id)
}

fn to_value(val: impl Serialize) -> Result<serde_json::Value, Error> {
    serde_json::to_value(val).map_err(|_err| {
        Error::Fatal {
            error: "Failed to serialize json value".into(),
        }
    })
}

fn invalid_raw_request() -> Error {
    Error::Retriable {
        error: "Could not parse JSON-RPC request".into(),
    }
}

#[derive(
    Debug, PartialEq, Eq, strum_macros::Display, EnumIter, FromPrimitive, ToPrimitive,
)]
pub enum InPageErrorCode {
    // Standard JSON-RPC codes
    // https://www.jsonrpc.org/specification
    ParseError,
    InvalidRequest,
    MethodNotFound,
    InvalidParams,
    InternalError,

    // Custom Ethereum Provider codes
    // https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1193.md#provider-errors
    UserRejected = 4001,
    Unauthorized = 4100,
    UnsupportedMethod = 4200,
    Disconnected = 4900,
    ChainDisconnected = 4901,
}

impl InPageErrorCode {
    fn to_i32(&self) -> i32 {
        ToPrimitive::to_i32(self).expect("error codes fit into i32")
    }
}

impl From<InPageErrorCode> for ErrorCode {
    fn from(code: InPageErrorCode) -> Self {
        match code {
            InPageErrorCode::ParseError => ErrorCode::ParseError,
            InPageErrorCode::InvalidRequest => ErrorCode::InvalidRequest,
            InPageErrorCode::MethodNotFound => ErrorCode::MethodNotFound,
            InPageErrorCode::InvalidParams => ErrorCode::InvalidParams,
            InPageErrorCode::InternalError => ErrorCode::InternalError,
            custom_code => ErrorCode::ServerError(custom_code.to_i32()),
        }
    }
}

impl From<InPageErrorCode> for ErrorObject<'static> {
    fn from(code: InPageErrorCode) -> Self {
        let code: ErrorCode = code.into();
        code.into()
    }
}

impl From<InPageErrorCode> for Error {
    fn from(code: InPageErrorCode) -> Self {
        let code: ErrorCode = code.into();
        Error::JsonRpc {
            code,
            message: code.to_string(),
        }
    }
}

impl From<CallError> for Error {
    fn from(error: CallError) -> Self {
        let error: ErrorObject = error.into();
        error.into()
    }
}

impl From<ErrorObject<'static>> for Error {
    fn from(error: ErrorObject) -> Self {
        let message = error.message();
        Error::JsonRpc {
            code: error.code().into(),
            message: message.into(),
        }
    }
}

pub fn load_in_page_provider_script(
    rpc_provider_name: &str,
    request_handler_name: &str,
) -> Result<String, Error> {
    let chain_id = eth::ChainId::default_dapp_chain();
    let network_version = chain_id.network_version();
    let hex_chain_id = chain_id.display_hex();
    let replacements = vec![
        (config::RPC_PROVIDER_PLACEHOLDER, rpc_provider_name),
        (config::REQUEST_HANDLER_PLACEHOLDER, request_handler_name),
        (config::DEFAULT_CHAIN_ID_PLACEHOLDER, &hex_chain_id),
        (config::DEFAULT_NETWORK_VERSION_PLACEHOLDER, &network_version),
    ];

    let path = format!(
        "{}/{}",
        config::JS_PREFIX,
        config::IN_PAGE_PROVIDER_FILE_NAME
    );
    let text = assets::load_asset_with_replacements(&path, replacements.iter())?;

    Ok(text)
}

// List maintained in https://docs.google.com/spreadsheets/d/1cHW7q_OblpMZpCxds5Es0sEYV6tySyKpHezh4TuXYOs
lazy_static! {
    static ref PROXIED_RPC_METHODS: HashSet<&'static str> = [
        "net_listening",
        "net_peerCount",
        "net_version",
        "eth_blockNumber",
        "eth_call",
        "eth_chainId",
        "eth_estimateGas",
        "eth_gasPrice",
        "eth_getBalance",
        "eth_getBlockByHash",
        "eth_getBlockByNumber",
        "eth_getBlockTransactionCountByHash",
        "eth_getBlockTransactionCountByNumber",
        "eth_getCode",
        "eth_getFilterChanges",
        "eth_getFilterLogs",
        "eth_getRawTransactionByHash",
        "eth_getRawTransactionByBlockHashAndIndex",
        "eth_getRawTransactionByBlockNumberAndIndex",
        "eth_getLogs",
        "eth_getStorageAt",
        "eth_getTransactionByBlockHashAndIndex",
        "eth_getTransactionByBlockNumberAndIndex",
        "eth_getTransactionByHash",
        "eth_getTransactionCount",
        "eth_getTransactionReceipt",
        "eth_getUncleByBlockHashAndIndex",
        "eth_getUncleByBlockNumberAndIndex",
        "eth_getUncleCountByBlockHash",
        "eth_getUncleCountByBlockNumber",
        "eth_getProof",
        "eth_newBlockFilter",
        "eth_newFilter",
        "eth_newPendingTransactionFilter",
        "eth_protocolVersion",
        "eth_sendRawTransaction",
        "eth_syncing",
        "eth_uninstallFilter",
    ]
    .into();
}

// More tests are in integrations tests in the [dev server.](tools/dev-server/static/ethereum.html)
#[cfg(test)]
mod tests {

    use super::*;
    use crate::db::data_migrations;
    use crate::db::schema_migrations::run_migrations;
    use anyhow::Result;
    use strum::IntoEnumIterator;

    struct TestInPageProvider {
        keychain: Keychain,
        connection_pool: ConnectionPool,
        public_suffix_list: PublicSuffixList,
        rpc_manager: Box<dyn eth::RpcManagerI>,
        http_client: HttpClient,
    }

    impl TestInPageProvider {
        pub fn new(page_url: &str) -> Self {
            let connection_pool =
                ConnectionPool::new(":memory:").expect("can start sqlite in memory");
            let rpc_manager = Box::new(eth::AnvilRpcManager::new());
            let public_suffix_list = PublicSuffixList::new().expect("can load PSL");
            // TODO the current tests won't make http requests, but if they do in the future, this
            // should be replace by a mock.
            let http_client = HttpClient::new_without_cache();
            let keychain = Keychain::new();
            // Run DB schema migrations and data migrations that haven't been applied yet.
            connection_pool
                .exclusive_transaction(|mut tx_conn| {
                    run_migrations(&mut tx_conn)?;
                    data_migrations::run_all(tx_conn, &keychain)
                })
                .expect("migrations succeed");

            Self {
                rpc_manager,
                public_suffix_list,
                connection_pool,
                keychain,
                http_client,
            }
        }

        fn provider(&self) -> InPageProvider {
            let context = InPageRequestContextMock::default_boxed();

            InPageProvider::new(
                &self.keychain,
                &self.connection_pool,
                &self.public_suffix_list,
                &*self.rpc_manager,
                &self.http_client,
                context,
            )
            .expect("url valid")
        }
    }

    impl<'a> Default for TestInPageProvider {
        fn default() -> Self {
            Self::new("http:/localhost:8080")
        }
    }

    #[test]
    fn proxy_checks_allowed_methods() -> Result<()> {
        let test: TestInPageProvider = Default::default();

        let result = test.connection_pool.deferred_transaction(|mut tx_conn| {
            test.provider()
                .proxy_method(&mut tx_conn, "eth_coinbase", ())
        });
        assert!(
            matches!(result, Err(Error::JsonRpc { code, .. }) if code == ErrorCode::ServerError(4200))
        );

        Ok(())
    }

    #[test]
    fn loads_in_page_provider_with_replace() -> Result<()> {
        let rpc_provider_name = "somethingUnlikelyToBeFoundInTheSource";
        let request_handler_name = "somethingElse.unlikely.to.be.found";

        let source =
            load_in_page_provider_script(rpc_provider_name, request_handler_name)?;

        let network_version = eth::ChainId::default_dapp_chain().network_version();
        let chain_id = eth::ChainId::default_dapp_chain().display_hex();

        assert!(source.contains(rpc_provider_name));
        assert!(source.contains(request_handler_name));
        assert!(source.contains(&network_version));
        assert!(source.contains(&chain_id));

        Ok(())
    }

    #[test]
    fn error_codes_fit_into_i32() {
        let mut sum = 0;
        for code in InPageErrorCode::iter() {
            // Test that conversion doesn't panic.
            sum += code.to_i32();
        }
        // Make sure loop isn't optimized away as noop.
        assert_ne!(sum, 0);
    }

    #[test]
    fn provider_events_start_with_lower_case() {
        for event in ProviderEvent::iter() {
            let s = serde_json::to_string(&event).unwrap();
            // First char is '"'
            let c = s.chars().nth(1).unwrap();
            assert!(c.is_lowercase());
        }
    }
}
