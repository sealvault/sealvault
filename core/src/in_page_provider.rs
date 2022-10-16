// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashSet, fmt::Debug, str::FromStr, sync::Arc};

use jsonrpsee::{
    core::server::helpers::MethodResponse,
    types::{
        error::{CallError, ErrorCode},
        ErrorObject, Params, Request,
    },
};
use lazy_static::lazy_static;
use num_traits::{FromPrimitive, ToPrimitive};
use serde::{Deserialize, Serialize};
use strum_macros::{EnumIter, EnumString};
use typed_builder::TypedBuilder;
use url::Url;

use crate::{
    app_core::CoreResources,
    assets, async_runtime as rt, config,
    db::{models as m, ConnectionPool},
    favicon::fetch_favicon_async,
    protocols::eth,
    CoreError, DappAllotmentTransferResult, Error,
};

#[derive(Debug)]
#[readonly::make]
pub(super) struct InPageProvider {
    resources: Arc<CoreResources>,
    request_context: Box<dyn InPageRequestContextI>,
    url: Url,
}

impl InPageProvider {
    pub(super) fn new(
        resources: Arc<CoreResources>,
        request_context: Box<dyn InPageRequestContextI>,
    ) -> Result<Self, Error> {
        let url = Url::parse(&request_context.page_url())?;
        Ok(Self {
            resources,
            request_context,
            url,
        })
    }

    fn connection_pool(&self) -> &ConnectionPool {
        &self.resources.connection_pool
    }

    // TODO add rate limiting
    // TODO refuse in page requests if dapp wasn't served over https or doesn't have a registrable
    // domain unless in dev mode.
    pub(super) fn in_page_request(
        self,
        raw_request: String,
    ) -> tokio::task::JoinHandle<Result<(), Error>> {
        rt::spawn(self.in_page_request_async(raw_request))
    }

    /// Response to a `CoreInPageCallbackI.request_dapp_approval`
    pub(super) fn user_approved_dapp(
        self,
        dapp_approval: DappApprovalParams,
    ) -> tokio::task::JoinHandle<Result<(), Error>> {
        rt::spawn(self.handle_user_approved_dapp(dapp_approval))
    }

    /// Respond to a `CoreInPageCallbackI.request_dapp_approval`
    pub(super) fn user_rejected_dapp(
        self,
        dapp_approval: DappApprovalParams,
    ) -> tokio::task::JoinHandle<Result<(), Error>> {
        rt::spawn(self.handle_user_rejected_dapp(dapp_approval))
    }

    async fn in_page_request_async(self, raw_request: String) -> Result<(), Error> {
        match self.raw_json_rpc_request(raw_request).await? {
            None => {
                // We're waiting for a dapp approval callback from the UI, so no response.
            }
            Some(response) => self.respond_to_request(response).await?,
        }
        Ok(())
    }

    async fn raw_json_rpc_request(
        &self,
        raw_request: String,
    ) -> Result<Option<MethodResponse>, Error> {
        let req = parse_request(&raw_request)?;
        match self.dispatch(&req).await {
            Ok(None) => Ok(None),
            Ok(Some(result)) => Ok(Some(MethodResponse::response(
                req.id,
                result,
                config::MAX_JSONRPC_RESPONSE_SIZE_BYTES,
            ))),
            Err(Error::JsonRpc { code, message }) => {
                // We need to select a data type even though data is none, <String>
                let data: Option<String> = None;
                let error_object = ErrorObject::owned(code.code(), message, data);
                Ok(Some(MethodResponse::error(req.id, error_object)))
            }
            Err(error) => Err(error),
        }
    }

    /// Resolve JSON-RPC method.
    async fn dispatch<'a>(
        &self,
        request: &'a Request<'a>,
    ) -> Result<Option<serde_json::Value>, Error> {
        let maybe_session = self.fetch_session_for_approved_dapp().await?;
        match &*request.method {
            // These methods request the user approval if the user hasn't added the dapp yet
            // in the account.
            "eth_requestAccounts" | "eth_accounts" => match maybe_session {
                Some(session) => {
                    let accounts = self.eth_request_accounts(session).await?;
                    Ok(Some(accounts))
                }
                None => {
                    self.request_add_new_dapp(request).await?;
                    Ok(None)
                }
            },
            _ => match maybe_session {
                Some(session) => {
                    let res = self.dispatch_authorized_methods(request, session).await?;
                    Ok(Some(res))
                }
                None => {
                    let err: Error = InPageErrorCode::Unauthorized.into();
                    Err(err)
                }
            },
        }
    }

    /// Resolve JSON-RPC method if user has approved the dapp in the current account.
    async fn dispatch_authorized_methods<'a>(
        &self,
        request: &'a Request<'a>,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        // let params = Params::new(request.params.map(|params| params.get()));
        match &*request.method {
            "eth_chainId" => self.eth_chain_id(session),
            "eth_sendTransaction" => {
                self.eth_send_transaction(request.params, session).await
            }
            "personal_sign" => self.personal_sign(request.params, session).await,
            "wallet_addEthereumChain" => self.wallet_add_ethereum_chain(request.params),
            "wallet_switchEthereumChain" => {
                self.wallet_switch_ethereum_chain(request.params, session)
                    .await
            }
            "web3_clientVersion" => self.web3_client_version(),
            "web3_sha3" => self.web3_sha3(request.params).await,
            method => self.proxy_method(method, request.params, session).await,
        }
    }

    async fn respond_to_request(&self, response: MethodResponse) -> Result<(), Error> {
        let callbacks = self.request_context.callbacks();
        rt::spawn_blocking(move || {
            // Prevent reflected XSS by passing the result as hexadecimal utf-8 bytes to JS.
            // See the security model in the developer docs for more.
            let hex_response = hex::encode(response.result.as_bytes());
            callbacks.respond(hex_response);
            Ok(())
        })
        .await?
    }

    /// Notify the in-page JS about an event in the background.
    async fn notify(&self, message: ProviderMessage) -> Result<(), Error> {
        let callbacks = self.request_context.callbacks();
        rt::spawn_blocking(move || {
            let json_message =
                serde_json::to_string(&message).map_err(|_| Error::Fatal {
                    error: format!(
                        "Failed to deserialize message for event: '{:?}'",
                        message.event
                    ),
                })?;
            let message_hex = hex::encode(json_message);
            callbacks.notify(message_hex);
            Ok(())
        })
        .await?
    }

    async fn notify_connect(
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
        self.notify(message).await
    }

    async fn notify_chain_changed(&self, chain_id: eth::ChainId) -> Result<(), Error> {
        let chain_id_json = chain_id_to_hex_str_json(chain_id)?;
        let chain_message = ProviderMessage {
            event: ProviderEvent::ChainChanged,
            data: chain_id_json,
        };
        self.notify(chain_message).await?;

        let network_version = chain_id.network_version();
        let network_version =
            serde_json::to_value(&network_version).map_err(|err| Error::Fatal {
                error: err.to_string(),
            })?;
        let network_message = ProviderMessage {
            event: ProviderEvent::NetworkChanged,
            data: network_version,
        };
        self.notify(network_message).await
    }

    async fn proxy_method<T>(
        &self,
        method: &str,
        params: T,
        session: m::LocalDappSession,
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

        let provider = self
            .resources
            .rpc_manager
            .eth_api_provider(session.chain_id);
        provider.proxy_rpc_request_async(method, params).await
    }

    fn eth_chain_id(
        &self,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        let chain_id: ethers::core::types::U64 = session.chain_id.into();
        let result = to_value(chain_id)?;
        Ok(result)
    }

    async fn eth_request_accounts(
        &self,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        let session = self
            .connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                session.update_last_used_at(&mut tx_conn)
            })
            .await?;

        self.notify_connect(session.chain_id, &session.address)
            .await?;

        let m::LocalDappSession { address, .. } = session;
        let result = to_value(vec![address])?;
        Ok(result)
    }

    async fn request_add_new_dapp<'a>(
        &self,
        request: &'a Request<'a>,
    ) -> Result<(), Error> {
        let resources = self.resources.clone();
        let account_id = rt::spawn_blocking(move || {
            let mut conn = resources.connection_pool.connection()?;
            m::LocalSettings::fetch_active_account_id(&mut conn)
        })
        .await??;

        let url = self.url.clone();
        let callbacks = self.request_context.callbacks();
        let favicon = self.fetch_favicon().await?;
        let dapp_identifier =
            m::Dapp::dapp_identifier(url, &self.resources.public_suffix_list)?;
        let raw_request =
            serde_json::to_string(request).map_err(|_| Error::Retriable {
                error: format!("Failed to serialize request id {:?}", request.id),
            })?;
        let dapp_approval = DappApprovalParams::builder()
            .account_id(account_id)
            .dapp_identifier(dapp_identifier)
            .favicon(favicon)
            .json_rpc_request(raw_request)
            .build();

        rt::spawn_blocking(move || {
            callbacks.request_dapp_approval(dapp_approval);
        })
        .await?;

        Ok(())
    }

    async fn handle_user_approved_dapp(
        self,
        dapp_approval: DappApprovalParams,
    ) -> Result<(), Error> {
        let request = parse_request(&dapp_approval.json_rpc_request)?;
        let session = self.add_new_dapp(dapp_approval.clone()).await?;
        let accounts = self.eth_request_accounts(session).await?;
        let response = MethodResponse::response(
            request.id,
            accounts,
            config::MAX_JSONRPC_RESPONSE_SIZE_BYTES,
        );
        self.respond_to_request(response).await?;
        Ok(())
    }

    async fn handle_user_rejected_dapp(
        self,
        dapp_approval: DappApprovalParams,
    ) -> Result<(), Error> {
        let request = parse_request(&dapp_approval.json_rpc_request)?;
        let err: ErrorObject = InPageErrorCode::UserRejected.into();
        let response = MethodResponse::error(request.id, err);
        self.respond_to_request(response).await?;
        Ok(())
    }

    /// Add a new dapp to the account and return the dapp's deterministic id.
    /// Also transfers the configured default amount to the new dapp address.
    async fn add_new_dapp(
        &self,
        dapp_approval: DappApprovalParams,
    ) -> Result<m::LocalDappSession, Error> {
        // Add dapp to account and create local session
        let url = self.url.clone();
        let resources = self.resources.clone();
        let session = self
            .connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                let chain_id = eth::ChainId::default_dapp_chain();
                let dapp_id = m::Dapp::create_if_not_exists(
                    &mut tx_conn,
                    url,
                    &resources.public_suffix_list,
                )?;
                m::Address::create_eth_key_and_address(
                    &mut tx_conn,
                    &resources.keychain,
                    &dapp_approval.account_id,
                    chain_id,
                    Some(&dapp_id),
                    false,
                )?;
                let params = m::DappSessionParams::builder()
                    .dapp_id(&dapp_id)
                    .account_id(&dapp_approval.account_id)
                    .chain_id(chain_id)
                    .build();
                m::LocalDappSession::create_eth_session(&mut tx_conn, &params)
            })
            .await?;

        // Transfer default dapp allotment to new dapp address from account wallet.
        self.transfer_default_dapp_allotment(session.clone())
            .await?;

        Ok(session)
    }

    async fn transfer_default_dapp_allotment(
        &self,
        session: m::LocalDappSession,
    ) -> Result<(), Error> {
        let resources = self.resources.clone();
        let session_clone = session.clone();
        let (chain_settings, wallet_signing_key) = self
            .connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                let wallet_address_id = m::Address::fetch_eth_wallet_id(
                    &mut tx_conn,
                    &session.account_id,
                    session.chain_id,
                )?;
                let chain_settings = m::Chain::fetch_user_settings_for_eth_chain(
                    tx_conn.as_mut(),
                    session.chain_id,
                )?;
                let wallet_signing_key = m::Address::fetch_eth_signing_key(
                    &mut tx_conn,
                    &resources.keychain,
                    &wallet_address_id,
                )?;
                Ok((chain_settings, wallet_signing_key))
            })
            .await?;
        if !chain_settings.default_dapp_allotment.amount.is_zero() {
            // Call blockchain API in background.
            rt::spawn(Self::make_default_dapp_allotment_transfer(
                self.resources.clone(),
                chain_settings,
                wallet_signing_key,
                session_clone,
            ));
        }
        Ok(())
    }

    async fn make_default_dapp_allotment_transfer(
        resources: Arc<CoreResources>,
        chain_settings: eth::ChainSettings,
        wallet_signing_key: eth::SigningKey,
        session: m::LocalDappSession,
    ) -> Result<(), Error> {
        let provider = resources
            .rpc_manager
            .eth_api_provider(wallet_signing_key.chain_id);
        // Call fails if there are insufficient funds.
        let res = provider
            .transfer_native_token_async(
                &wallet_signing_key,
                &session.address,
                &chain_settings.default_dapp_allotment,
            )
            .await;
        rt::spawn_blocking(move || {
            let mut conn = resources.connection_pool.connection()?;
            let dapp_identifier = session.fetch_dapp_identifier(&mut conn)?;

            let eth::ChainSettings {
                default_dapp_allotment: amount,
                ..
            } = chain_settings;
            let mut callback_result = DappAllotmentTransferResult::builder()
                .dapp_identifier(dapp_identifier)
                .amount(amount.display_amount())
                .token_symbol(amount.chain_id.native_token().symbol())
                .chain_display_name(amount.chain_id.display_name())
                .build();

            match res {
                Ok(_) => {
                    resources
                        .ui_callbacks
                        .dapp_allotment_transfer_result(callback_result);
                }
                Err(err) => {
                    log::error!(
                        "Failed to transfer allotment to new dapp due to error: {}",
                        err
                    );
                    // In CoreError RPC errors that can be displayed to users are converted to
                    // CoreError::User.
                    let error: CoreError = err.into();
                    match error {
                        CoreError::User { explanation } => {
                            callback_result.error_message = Some(explanation)
                        }
                        _ => {
                            callback_result.error_message =
                                Some("An unexpected error occurred".into())
                        }
                    }
                    resources
                        .ui_callbacks
                        .dapp_allotment_transfer_result(callback_result);
                }
            }
            Ok(())
        })
        .await?
    }

    async fn fetch_session_for_approved_dapp(
        &self,
    ) -> Result<Option<m::LocalDappSession>, Error> {
        let url = self.url.clone();
        let resources = self.resources.clone();
        self.connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                let account_id =
                    m::LocalSettings::fetch_active_account_id(tx_conn.as_mut())?;
                let maybe_dapp_id = m::Dapp::fetch_id_for_account(
                    tx_conn.as_mut(),
                    url,
                    &resources.public_suffix_list,
                    &account_id,
                )?;
                // If the dapp has been added to the account, return an existing session or create one.
                // It can happen that the dapp has been added, but no local session exists if the dapp
                // was added on an other device.
                let maybe_session: Option<m::LocalDappSession> = match maybe_dapp_id {
                    Some(dapp_id) => {
                        let params = m::DappSessionParams::builder()
                            .dapp_id(&dapp_id)
                            .account_id(&account_id)
                            .build();
                        let session =
                            m::LocalDappSession::create_eth_session_if_not_exists(
                                &mut tx_conn,
                                &params,
                            )?;
                        Some(session)
                    }
                    None => None,
                };
                Ok(maybe_session)
            })
            .await
    }

    async fn eth_send_transaction(
        &self,
        params: Option<&serde_json::value::RawValue>,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        let signing_key = self.fetch_eth_signing_key(session).await?;

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

        let provider = self
            .resources
            .rpc_manager
            .eth_api_provider(signing_key.chain_id);
        let tx_hash = provider.send_transaction_async(&signing_key, tx).await?;

        to_value(tx_hash)
    }

    async fn personal_sign(
        &self,
        params: Option<&serde_json::value::RawValue>,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        let params = Params::new(params.map(|params| params.get()));
        let mut params = params.sequence();
        let message: String = params.next()?;
        let message = decode_0x_hex_prefix(&message)?;
        let request_address: ethers::core::types::Address =
            ethers::core::types::Address::from_str(&session.address)
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

        let signing_key = self.fetch_eth_signing_key(session).await?;
        rt::spawn_blocking(move || {
            let signer = eth::Signer::new(&signing_key);
            let signature = signer.personal_sign(message)?;
            to_value(signature.to_string())
        })
        .await?
    }

    /// We don't support adding chains that aren't supported already, so this is a noop if the chain
    /// is already supported and an error if it isn't.
    fn wallet_add_ethereum_chain(
        &self,
        params: Option<&serde_json::value::RawValue>,
    ) -> Result<serde_json::Value, Error> {
        let params = Params::new(params.map(|params| params.get()));
        let chain_params: AddEthereumChainParameter = params.sequence().next()?;
        // If we can parse it, it's a supported chain id which means it was "added".
        let _chain_id: eth::ChainId = parse_0x_chain_id(&chain_params.chain_id)?;
        // Result should be null on success. We need type annotations for serde.
        let result: Option<String> = None;
        to_value(result)
    }

    async fn wallet_switch_ethereum_chain(
        &self,
        params: Option<&serde_json::value::RawValue>,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        let params = Params::new(params.map(|params| params.get()));
        let chain_id: SwitchEthereumChainParameter = params.sequence().next()?;
        // If we can parse the chain, then it's supported.
        let new_chain_id: eth::ChainId = parse_0x_chain_id(&chain_id.chain_id)?;

        self.resources
            .connection_pool
            .deferred_transaction_async(move |mut tx_conn| {
                let chain_entity_id =
                    m::Chain::fetch_or_create_eth_chain_id(&mut tx_conn, new_chain_id)?;

                let asymmetric_key_id =
                    m::Address::fetch_key_id(tx_conn.as_mut(), &session.address_id)?;
                let address_entity = m::AddressEntity::builder()
                    .asymmetric_key_id(&asymmetric_key_id)
                    .chain_entity_id(&chain_entity_id)
                    .build();
                let new_address_id = m::Address::fetch_or_create_for_eth_chain(
                    &mut tx_conn,
                    &address_entity,
                )?;

                session.update_session_address(&mut tx_conn, &new_address_id)
            })
            .await?;

        self.notify_chain_changed(new_chain_id).await?;

        // Result should be null on success. We need type annotations for serde.
        let result: Option<String> = None;
        to_value(result)
    }

    fn web3_client_version(&self) -> Result<serde_json::Value, Error> {
        Ok("SealVault".into())
    }

    async fn web3_sha3(
        &self,
        params: Option<&serde_json::value::RawValue>,
    ) -> Result<serde_json::Value, Error> {
        let params = Params::new(params.map(|params| params.get()));
        let mut params = params.sequence();
        let message: String = params.next()?;
        rt::spawn_blocking(move || {
            let message = decode_0x_hex_prefix(&message)?;
            let hash = ethers::core::utils::keccak256(message);
            let result = format!("0x{}", hex::encode(hash));
            to_value(result)
        })
        .await?
    }

    async fn fetch_eth_signing_key(
        &self,
        session: m::LocalDappSession,
    ) -> Result<eth::SigningKey, Error> {
        let resources = self.resources.clone();
        let signing_key: eth::SigningKey = self
            .connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                m::Address::fetch_eth_signing_key(
                    &mut tx_conn,
                    &resources.keychain,
                    &session.address_id,
                )
            })
            .await?;
        Ok(signing_key)
    }

    async fn fetch_favicon(&self) -> Result<Option<Vec<u8>>, Error> {
        let client = &self.resources.http_client;
        let favicon = fetch_favicon_async(client, self.url.clone()).await?;
        Ok(favicon)
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
    /// The JSON-RPC request that requested adding this dapp.
    #[builder(setter(into))]
    pub json_rpc_request: String,
}

pub trait CoreInPageCallbackI: Send + Sync + Debug {
    /// Request a dapp approval from the user through the UI.
    /// After the user has approved the dapp for the first time, it'll be allowed to connect and
    /// execute transactions automatically.
    fn request_dapp_approval(&self, dapp_approval: DappApprovalParams);

    /// Respond to an in-page provider request.
    fn respond(&self, response_hex: String);

    /// Notify the in-page provider of an event.
    fn notify(&self, event_hex: String);
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

fn parse_request(raw_request: &str) -> Result<Request, Error> {
    if raw_request.as_bytes().len() > config::MAX_JSONRPC_REQUEST_SIZE_BYTES {
        return Err(invalid_raw_request());
    }
    let req: Request =
        serde_json::from_str(raw_request).map_err(|_| invalid_raw_request())?;
    Ok(req)
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
    serde_json::to_value(val).map_err(|_err| Error::Fatal {
        error: "Failed to serialize json value".into(),
    })
}

fn invalid_raw_request() -> Error {
    // We can only return JSON RPC message with error if we can parse the message,
    // because we need the request id for that, hence the retriable error here.
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
        (
            config::DEFAULT_NETWORK_VERSION_PLACEHOLDER,
            &network_version,
        ),
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
    use anyhow::Result;
    use jsonrpsee::types::Id;
    use strum::IntoEnumIterator;

    use super::*;
    use crate::{app_core::tests::TmpCore, utils::new_uuid};

    const ETH_REQUEST_ACCOUNTS: &str = "eth_requestAccounts";
    const ETH_CHAIN_ID: &str = "eth_chainId";

    impl InPageProvider {
        fn call_no_arg(self, method: &str) -> Result<()> {
            let id = new_uuid();
            let request = Request::new(method.into(), None, Id::Str(id.into()));
            let raw_request =
                serde_json::to_string(&request).expect("request serializes");
            let handle = self.in_page_request(raw_request);
            rt::block_on(handle)??;
            Ok(())
        }
    }

    fn authorize_dapp(core: &TmpCore) -> Result<()> {
        let provider = core.in_page_provider(true);
        provider.call_no_arg(ETH_REQUEST_ACCOUNTS)?;
        core.wait_for_first_in_page_response();
        Ok(())
    }

    #[test]
    fn responds_on_allowed() -> Result<()> {
        let core = TmpCore::new()?;

        authorize_dapp(&core)?;

        assert!(core.dapp_approval().is_some());
        assert_eq!(core.responses().len(), 1);
        assert_eq!(core.notifications().len(), 1);
        core.wait_for_dapp_allotment_transfer();
        let dapp_allotment_results = core.dapp_allotment_transfer_results();
        assert_eq!(dapp_allotment_results.len(), 1);
        let dapp_host = core
            .dapp_url()
            .host()
            .expect("dapp url has host")
            .to_string();
        assert_eq!(dapp_allotment_results[0].dapp_identifier, dapp_host);

        Ok(())
    }

    #[test]
    fn disallows_un_approved() -> Result<()> {
        let core = TmpCore::new()?;

        let provider = core.in_page_provider(false);
        provider.call_no_arg(ETH_CHAIN_ID)?;

        let responses = core.responses();
        assert!(core.dapp_approval().is_none());
        assert_eq!(responses.len(), 1);
        assert_eq!(core.notifications().len(), 0);

        let unauthorized = InPageErrorCode::Unauthorized.to_i32().to_string();
        assert!(responses[0].contains(&unauthorized));

        Ok(())
    }

    #[test]
    fn proxy_checks_allowed_methods() -> Result<()> {
        let core = TmpCore::new()?;

        authorize_dapp(&core)?;

        // This request should be refused as it's an unsupported method
        let provider = core.in_page_provider(true);
        provider.call_no_arg("eth_coinbase")?;

        let responses = core.responses();
        assert!(core.dapp_approval().is_some());
        assert_eq!(responses.len(), 2);

        let unsupported = InPageErrorCode::UnsupportedMethod.to_i32().to_string();
        assert!(responses[1].contains(&unsupported));

        Ok(())
    }

    #[test]
    fn proxied_method_ok() -> Result<()> {
        let core = TmpCore::new()?;

        authorize_dapp(&core)?;

        let provider = core.in_page_provider(true);
        provider.call_no_arg("eth_gasPrice")?;

        let responses = core.responses();
        assert_eq!(responses.len(), 2);

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
