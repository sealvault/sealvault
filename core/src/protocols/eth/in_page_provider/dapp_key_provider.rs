// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{fmt::Debug, sync::Arc};

use ethers::types::{Address, Bytes, TransactionRequest, H256};
use jsonrpsee::{
    core::server::helpers::MethodResponse,
    types::{error::ErrorCode, ErrorObject, Request},
};
use num_traits::ToPrimitive;
use serde::{Deserialize, Serialize};
use serde_json::json;
use strum_macros::{EnumIter, EnumString};
use typed_builder::TypedBuilder;
use url::Url;

use crate::{
    async_runtime as rt, config,
    db::{models as m, ConnectionPool, DeterministicId},
    encryption::Keychain,
    favicon::fetch_favicon_async,
    http_client::HttpClient,
    protocols::eth::{
        explorer,
        in_page_provider::in_page_request::{
            AddEthereumChainParameter, InPageRequest, InPageRequestParams,
            SwitchEthereumChainParameter,
        },
        ChainId, ChainSettings, ChecksumAddress, EncryptedSigningKey, RpcManagerI,
        Signer,
    },
    public_suffix_list::PublicSuffixList,
    resources::CoreResourcesI,
    ui_callback::{DappSignatureResult, DappTransactionApproved, DappTransactionResult},
    CoreError, DappAllotmentTransferResult, Error,
};

#[derive(Debug)]
#[readonly::make]
pub struct DappKeyProvider {
    resources: Arc<dyn CoreResourcesI>,
    request_context: Box<dyn InPageRequestContextI>,
    url: Url,
}

impl DappKeyProvider {
    pub fn new(
        resources: Arc<dyn CoreResourcesI>,
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
        self.resources.connection_pool()
    }

    fn rpc_manager(&self) -> &dyn RpcManagerI {
        self.resources.rpc_manager()
    }

    fn public_suffix_list(&self) -> &PublicSuffixList {
        self.resources.public_suffix_list()
    }

    fn http_client(&self) -> &HttpClient {
        self.resources.http_client()
    }

    fn keychain(&self) -> &Keychain {
        self.resources.keychain()
    }

    // TODO add rate limiting
    // TODO refuse in page requests if dapp wasn't served over https or doesn't have a registrable
    // domain unless in dev mode.
    pub(crate) fn in_page_request(
        self,
        raw_request: String,
    ) -> tokio::task::JoinHandle<Result<(), Error>> {
        rt::spawn(self.in_page_request_async(raw_request))
    }

    /// Response to a `CoreInPageCallbackI.request_dapp_approval`
    pub(crate) fn user_approved_dapp(
        self,
        dapp_approval: DappApprovalParams,
    ) -> tokio::task::JoinHandle<Result<(), Error>> {
        rt::spawn(self.handle_user_approved_dapp(dapp_approval))
    }

    /// Respond to a `CoreInPageCallbackI.request_dapp_approval`
    pub(crate) fn user_rejected_dapp(
        self,
        dapp_approval: DappApprovalParams,
    ) -> tokio::task::JoinHandle<Result<(), Error>> {
        rt::spawn(self.handle_user_rejected_dapp(dapp_approval))
    }

    pub async fn in_page_request_async(self, raw_request: String) -> Result<(), Error> {
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
        let request = parse_request(&raw_request)?;

        let call = json!({
            "method": request.method,
            "params": request.params
        });
        let in_page_request: Result<InPageRequest, _> = serde_json::from_value(call);

        match in_page_request {
            Ok(in_page_request) => {
                match self.dispatch(in_page_request, &raw_request).await {
                    Ok(None) => Ok(None),
                    Ok(Some(result)) => Ok(Some(MethodResponse::response(
                        request.id,
                        result,
                        config::MAX_JSONRPC_RESPONSE_SIZE_BYTES,
                    ))),
                    Err(Error::JsonRpc { code, message }) => {
                        // We need to select a data type even though data is none, <String>
                        let data: Option<String> = None;
                        let error_object = ErrorObject::owned(code.code(), message, data);
                        Ok(Some(MethodResponse::error(request.id, error_object)))
                    }
                    Err(error) => Err(error),
                }
            }
            Err(err) => {
                let message = err.to_string();
                // TODO there is probably a better way to handle this
                let code = if message.contains("unknown variant") {
                    InPageErrorCode::MethodNotFound
                } else {
                    InPageErrorCode::InvalidParams
                };
                let data: Option<String> = None;
                let error_object = ErrorObject::owned(code.to_i32(), message, data);
                Ok(Some(MethodResponse::error(request.id, error_object)))
            }
        }
    }

    /// Resolve JSON-RPC method.
    async fn dispatch<'a>(
        &self,
        request: InPageRequest,
        raw_request: &str,
    ) -> Result<Option<serde_json::Value>, Error> {
        let maybe_session = self.fetch_session_for_approved_dapp().await?;
        match request {
            InPageRequest::EthAccounts(..) if maybe_session.is_none() => {
                self.request_add_new_dapp(raw_request).await?;
                Ok(None)
            }
            // MetaMask exposes chain id and net version even if the user didn't authorize the dapp.
            InPageRequest::EthChainId(..) if maybe_session.is_none() => {
                Ok(Some(self.eth_chain_id_unauthorized()?))
            }
            InPageRequest::EthNetworkId(..) if maybe_session.is_none() => {
                Ok(Some(self.net_version_unauthorized()?))
            }
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

    /// Resolve JSON-RPC method if user has approved the dapp in the current profile.
    async fn dispatch_authorized_methods<'a>(
        &self,
        request: InPageRequest,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        // let params = Params::new(request.params.map(|params| params.get()));
        match request {
            InPageRequest::EthAccounts(..) => self.eth_request_accounts(session).await,
            InPageRequest::EthChainId(..) => self.eth_chain_id(session),
            InPageRequest::EthSendTransaction(tx) => {
                self.eth_send_transaction(tx, session).await
            }
            InPageRequest::PersonalSign(message, address, password) => {
                self.personal_sign(message, address, password, session)
                    .await
            }
            InPageRequest::WalletAddEthereumChain(param) => {
                self.wallet_add_ethereum_chain(param, session).await
            }
            InPageRequest::WalletSwitchEthereumChain(param) => {
                self.wallet_switch_ethereum_chain(param, session).await
            }
            InPageRequest::Web3ClientVersion(..) => self.web3_client_version(),
            InPageRequest::Web3Sha3(payload) => self.web3_sha3(payload).await,
            request => self.proxy_method(request, session).await,
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
        chain_id: ChainId,
        selected_address: ChecksumAddress,
    ) -> Result<(), Error> {
        let network_version = chain_id.network_version();
        let event = SealVaultConnect {
            chain_id: chain_id.into(),
            network_version: &network_version,
            selected_address,
        };
        let data = serde_json::to_value(&event).map_err(|_| Error::Fatal {
            error: format!("Failed to deserialize SealVaultConnect event: {event:?}"),
        })?;
        let message = ProviderMessage {
            event: ProviderEvent::SealVaultConnect,
            data,
        };
        self.notify(message).await
    }

    async fn notify_chain_changed(&self, chain_id: ChainId) -> Result<(), Error> {
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

    async fn proxy_method(
        &self,
        request: InPageRequest,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        if !request.allow_proxy() {
            // Must return 4200 for unsupported method for Ethereum
            // https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1193.md#supported-rpc-methods
            return Err(Error::JsonRpc {
                code: InPageErrorCode::UnsupportedMethod.into(),
                message: format!("This method is not supported: '{}'", request),
            });
        }

        let provider = self.rpc_manager().eth_api_provider(session.chain_id);
        let InPageRequestParams { method, params } = request.try_into()?;
        provider.proxy_rpc_request_async(&method, params).await
    }

    fn eth_chain_id(
        &self,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        let chain_id: ethers::core::types::U64 = session.chain_id.into();
        let result = to_value(chain_id)?;
        Ok(result)
    }

    // Only ok to expose unauthorized if we respond to all requests with the same response,
    // otherwise it's a privacy leak.
    fn eth_chain_id_unauthorized(&self) -> Result<serde_json::Value, Error> {
        let chain_id = ChainId::default_dapp_chain();
        let chain_id: ethers::core::types::U64 = chain_id.into();
        let result = to_value(chain_id)?;
        Ok(result)
    }

    // Only ok to expose unauthorized if we respond to all requests with the same response,
    // otherwise it's a privacy leak.
    fn net_version_unauthorized(&self) -> Result<serde_json::Value, Error> {
        let chain_id = ChainId::default_dapp_chain();
        let result = to_value(chain_id.network_version())?;
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

        self.notify_connect(session.chain_id, session.address)
            .await?;

        let m::LocalDappSession { address, .. } = session;
        let result = to_value(vec![address])?;
        Ok(result)
    }

    async fn request_add_new_dapp<'a>(&self, raw_request: &str) -> Result<(), Error> {
        let resources = self.resources.clone();
        let (profile_id, chain_id, chain_settings) = resources
            .connection_pool()
            .deferred_transaction_async(|mut tx_conn| {
                let profile_id =
                    m::LocalSettings::fetch_active_profile_id(tx_conn.as_mut())?;
                let chain_id = ChainId::default_dapp_chain();
                let chain_settings = m::Chain::fetch_user_settings_for_eth_chain(
                    tx_conn.as_mut(),
                    chain_id,
                )?;
                Ok((profile_id, chain_id, chain_settings))
            })
            .await?;

        let url = self.url.clone();
        let callbacks = self.request_context.callbacks();
        let favicon = self.fetch_favicon().await?;
        let dapp_identifier = m::Dapp::dapp_identifier(url, self.public_suffix_list())?;
        let dapp_allotment = chain_settings.default_dapp_allotment;
        let dapp_approval = DappApprovalParams::builder()
            .profile_id(profile_id)
            .dapp_identifier(dapp_identifier)
            .favicon(favicon)
            .amount(dapp_allotment.display_amount())
            .transfer_allotment(!dapp_allotment.amount.is_zero())
            .token_symbol(chain_id.native_token().symbol())
            .chain_display_name(chain_id.display_name())
            .chain_id(chain_id)
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

    /// Add a new dapp to the profile and return the dapp's deterministic id.
    /// Also transfers the configured default amount to the new dapp address.
    async fn add_new_dapp(
        &self,
        dapp_approval: DappApprovalParams,
    ) -> Result<m::LocalDappSession, Error> {
        // Add dapp to profile and create local session
        let url = self.url.clone();
        let resources = self.resources.clone();
        let chain_id: ChainId = dapp_approval.chain_id.try_into()?;
        let profile_id: DeterministicId = dapp_approval.profile_id.try_into()?;
        let session = self
            .connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                let dapp_id = m::Dapp::create_if_not_exists(
                    &mut tx_conn,
                    url,
                    resources.public_suffix_list(),
                )?;
                let params = m::CreateEthAddressParams::builder()
                    .profile_id(&profile_id)
                    .chain_id(chain_id)
                    .dapp_id(Some(&dapp_id))
                    .build();
                m::Address::create_eth_key_and_address(
                    &mut tx_conn,
                    resources.keychain(),
                    &params,
                )?;
                let params = m::NewDappSessionParams::builder()
                    .dapp_id(&dapp_id)
                    .profile_id(&profile_id)
                    .chain_id(chain_id)
                    .build();
                m::LocalDappSession::create_eth_session(&mut tx_conn, &params)
            })
            .await?;

        // Transfer default dapp allotment to new dapp address from profile wallet.
        if dapp_approval.transfer_allotment {
            self.transfer_default_dapp_allotment(session.clone())
                .await?;
        }

        Ok(session)
    }

    async fn transfer_default_dapp_allotment(
        &self,
        session: m::LocalDappSession,
    ) -> Result<(), Error> {
        let session_clone = session.clone();
        let (chain_settings, encrypted_wallet_signing_key) = self
            .connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                let wallet_address_id = m::Address::fetch_eth_wallet_id(
                    &mut tx_conn,
                    &session.profile_id,
                    session.chain_id,
                )?;
                let chain_settings = m::Chain::fetch_user_settings_for_eth_chain(
                    tx_conn.as_mut(),
                    session.chain_id,
                )?;
                let encrypted_wallet_signing_key =
                    m::Address::fetch_encrypted_secret_key(
                        &mut tx_conn,
                        &wallet_address_id,
                    )?;
                Ok((chain_settings, encrypted_wallet_signing_key))
            })
            .await?;
        // Call blockchain API in background.
        rt::spawn(Self::make_default_dapp_allotment_transfer(
            self.resources.clone(),
            chain_settings,
            encrypted_wallet_signing_key,
            session_clone,
        ));
        Ok(())
    }

    async fn make_default_dapp_allotment_transfer(
        resources: Arc<dyn CoreResourcesI>,
        chain_settings: ChainSettings,
        wallet_signing_key: EncryptedSigningKey,
        session: m::LocalDappSession,
    ) -> Result<(), Error> {
        // Call fails if there are insufficient funds.
        let res = async {
            let provider = resources
                .rpc_manager()
                .eth_api_provider(wallet_signing_key.chain_id);
            let tx_hash = provider
                .transfer_native_token_async(
                    resources.keychain(),
                    &wallet_signing_key,
                    session.address,
                    &chain_settings.default_dapp_allotment,
                )
                .await?;
            provider.wait_for_confirmation_async(tx_hash).await?;
            Ok::<(), Error>(())
        }
        .await;
        rt::spawn_blocking(move || {
            let ChainSettings {
                default_dapp_allotment: amount,
                ..
            } = chain_settings;
            let m::LocalDappSession {
                dapp_human_identifier,
                ..
            } = session;

            let mut callback_result = DappAllotmentTransferResult::builder()
                .dapp_identifier(dapp_human_identifier)
                .amount(amount.display_amount())
                .token_symbol(amount.chain_id.native_token().symbol())
                .chain_display_name(amount.chain_id.display_name())
                .build();

            match res {
                Ok(_) => {
                    resources
                        .ui_callbacks()
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
                        .ui_callbacks()
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
                let profile_id =
                    m::LocalSettings::fetch_active_profile_id(tx_conn.as_mut())?;
                let maybe_dapp_id = m::Dapp::fetch_id_for_profile(
                    tx_conn.as_mut(),
                    url,
                    resources.public_suffix_list(),
                    &profile_id,
                )?;
                // If the dapp has been added to the profile, return an existing session or create one.
                // It can happen that the dapp has been added, but no local session exists if the dapp
                // was added on an other device.
                let maybe_session: Option<m::LocalDappSession> = match maybe_dapp_id {
                    Some(dapp_id) => {
                        let params = m::NewDappSessionParams::builder()
                            .dapp_id(&dapp_id)
                            .profile_id(&profile_id)
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
        mut tx: TransactionRequest,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        let (session, signing_key) =
            self.fetch_eth_encrypted_signing_key(session).await?;

        // Remove nonce to fill with latest nonce from remote API in signer to make sure tx nonce is
        // current. MetaMask does this too.
        tx.nonce = None;

        let provider = self.rpc_manager().eth_api_provider(signing_key.chain_id);

        let tx_hash_fut =
            provider.send_transaction_async(self.keychain(), &signing_key, tx);

        let resources = self.resources.clone();
        let session = Self::approved_dapp_transaction(resources, session).await;

        let tx_hash = tx_hash_fut.await;

        let resources = self.resources.clone();
        let tx_hash_res = tx_hash.clone();
        // Call in background.
        rt::spawn(async move {
            Self::dapp_transaction_result(resources, session, tx_hash_res).await;
        });

        to_value(tx_hash?)
    }

    async fn approved_dapp_transaction(
        resources: Arc<dyn CoreResourcesI>,
        session: m::LocalDappSession,
    ) -> m::LocalDappSession {
        let result = DappTransactionApproved::builder()
            .dapp_identifier(session.dapp_human_identifier.clone())
            .chain_display_name(session.chain_id.display_name())
            .build();

        let joined = rt::spawn_blocking(move || {
            resources
                .ui_callbacks()
                .approved_dapp_transaction(result.clone());
        })
        .await;
        if joined.is_err() {
            let dapp_identifier = &session.dapp_human_identifier;
            log::error!(
                "Failed to join dapp transaction approval for dapp '{dapp_identifier}'"
            );
        }

        session
    }

    async fn dapp_transaction_result(
        resources: Arc<dyn CoreResourcesI>,
        session: m::LocalDappSession,
        tx_hash_res: Result<H256, Error>,
    ) {
        let m::LocalDappSession {
            dapp_human_identifier,
            chain_id,
            ..
        } = session;
        let mut partial_result = DappTransactionResult::builder()
            .dapp_identifier(dapp_human_identifier)
            .chain_display_name(chain_id.display_name())
            .build();

        let result =
            match tx_hash_res {
                Ok(tx_hash) => {
                    let rpc_provider =
                        resources.rpc_manager().eth_api_provider(session.chain_id);
                    match rpc_provider.wait_for_confirmation_async(tx_hash).await {
                        Ok(tx_hash) => explorer::tx_url(session.chain_id, &tx_hash)
                            .ok()
                            .map(|url| {
                                partial_result.explorer_url = Some(url.to_string());
                                partial_result
                            }),
                        Err(err) => dapp_transaction_result_error(partial_result, err),
                    }
                }
                Err(err) => dapp_transaction_result_error(partial_result, err),
            };

        if let Some(result) = result {
            let joined = rt::spawn_blocking(move || {
                resources.ui_callbacks().dapp_transaction_result(result);
            })
            .await;
            if joined.is_err() {
                log::error!("Failed to join dapp_transaction_result callback future.")
            }
        };
    }

    async fn personal_sign(
        &self,
        message: Bytes,
        address: Address,
        _password: Option<String>, // Password argument is ignored.
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        if session.address != address {
            return Err(Error::JsonRpc {
                code: InPageErrorCode::InvalidParams.into(),
                message: "Invalid address".into(),
            });
        }

        let (session, signing_key) =
            self.fetch_eth_encrypted_signing_key(session).await?;
        let signer = Signer::new(self.keychain(), &signing_key);
        let signature = signer.personal_sign(message)?;

        let resources = self.resources.clone();
        // Call in background
        rt::spawn(Self::personal_sign_callback(resources, session));

        to_value(signature.to_string())
    }

    async fn personal_sign_callback(
        resources: Arc<dyn CoreResourcesI>,
        session: m::LocalDappSession,
    ) {
        let m::LocalDappSession {
            dapp_human_identifier,
            ..
        } = session;
        let result = DappSignatureResult::builder()
            .dapp_identifier(dapp_human_identifier)
            .build();
        let joined = rt::spawn_blocking(move || {
            resources.ui_callbacks().signed_message_for_dapp(result);
        })
        .await;
        if joined.is_err() {
            log::error!("Failed to join signed_message_for_dapp callback future.")
        }
    }

    /// We don't support adding chains that aren't supported already, so this is a noop if the chain
    /// is already supported and an error if it isn't.
    /// It changes the current chain to the "added" one to follow MetaMask behaviour.
    async fn wallet_add_ethereum_chain(
        &self,
        param: AddEthereumChainParameter,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        // If we can parse it, it's a supported chain id which means it was "added".
        let new_chain_id: ChainId = parse_0x_chain_id(&param.chain_id)?;

        // We change the chain automatically, because MM requests user approval to change the chain
        // after a new one was added:
        // https://github.com/MetaMask/metamask-mobile/blob/bdb7f37c90e4fc923881a07fca38d4e77c73a579/app/core/RPCMethods/wallet_addEthereumChain.js#L303
        // This is safe, because we don't allow adding arbitrary chains.
        // Some dapps depend on this behaviour. See https://github.com/sealvault/sealvault/issues/24
        // for example.
        self.change_eth_chain(session, new_chain_id).await?;

        // Result should be null on success. We need type annotations for serde.
        let result: Option<String> = None;
        to_value(result)
    }

    async fn wallet_switch_ethereum_chain(
        &self,
        param: SwitchEthereumChainParameter,
        session: m::LocalDappSession,
    ) -> Result<serde_json::Value, Error> {
        // If we can parse the chain, then it's supported.
        // MetaMask returns error code 4902 if the chain has not been added yet so that the dapp can
        // request adding it. We don't do that, because we don't support adding arbitrary chains.
        let new_chain_id: ChainId = parse_0x_chain_id(&param.chain_id)?;

        self.change_eth_chain(session, new_chain_id).await?;

        // Result should be null on success. We need type annotations for serde.
        let result: Option<String> = None;
        to_value(result)
    }

    async fn change_eth_chain(
        &self,
        session: m::LocalDappSession,
        new_chain_id: ChainId,
    ) -> Result<(), Error> {
        self.connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                session.change_eth_chain(&mut tx_conn, new_chain_id)
            })
            .await?;

        self.notify_chain_changed(new_chain_id).await?;

        Ok(())
    }

    fn web3_client_version(&self) -> Result<serde_json::Value, Error> {
        Ok("SealVault".into())
    }

    async fn web3_sha3(&self, payload: Bytes) -> Result<serde_json::Value, Error> {
        rt::spawn_blocking(move || {
            let hash = ethers::core::utils::keccak256(payload);
            let result = format!("0x{}", hex::encode(hash));
            to_value(result)
        })
        .await?
    }

    async fn fetch_eth_encrypted_signing_key(
        &self,
        session: m::LocalDappSession,
    ) -> Result<(m::LocalDappSession, EncryptedSigningKey), Error> {
        let (session, encrypted_secret_key) = self
            .connection_pool()
            .deferred_transaction_async(move |mut tx_conn| {
                let encrypted_secret_key = m::Address::fetch_encrypted_secret_key(
                    &mut tx_conn,
                    &session.address_id,
                )?;
                Ok((session, encrypted_secret_key))
            })
            .await?;
        Ok((session, encrypted_secret_key))
    }

    async fn fetch_favicon(&self) -> Result<Option<Vec<u8>>, Error> {
        let client = self.http_client();
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
    /// The profile for which the dapp approval is set.
    #[builder(setter(into))]
    pub profile_id: String,
    /// A human readable dapp identifier that can be presented to the user.
    #[builder(setter(into))]
    pub dapp_identifier: String,
    /// The dapps favicon
    #[builder(setter(into))]
    pub favicon: Option<Vec<u8>>,
    /// The amount that is to be transferred to the dapp address.
    #[builder(setter(into))]
    pub amount: String,
    /// Whether to transfer the dapp allotment.
    #[builder(setter(into))]
    pub transfer_allotment: bool,
    /// The symbol of the token that was transferred.
    #[builder(setter(into))]
    pub token_symbol: String,
    /// The displayable name of the chain where the token was transferred.
    #[builder(setter(into))]
    pub chain_display_name: String,
    #[builder(setter(into))]
    pub chain_id: u64,
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
    selected_address: ChecksumAddress,
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

fn parse_0x_chain_id(hex_chain_id: &str) -> Result<ChainId, Error> {
    // U64 should support
    let chain_id = strip_0x_hex_prefix(hex_chain_id)?;
    let chain_id =
        ethers::core::types::U64::from_str_radix(chain_id, 16).map_err(|_| {
            Error::JsonRpc {
                code: InPageErrorCode::InvalidParams.into(),
                message: "Invalid U64".into(),
            }
        })?;
    let chain_id: ChainId = chain_id.try_into().map_err(|_| Error::JsonRpc {
        code: InPageErrorCode::InvalidParams.into(),
        message: "Unsupported chain id".into(),
    })?;
    Ok(chain_id)
}

fn chain_id_to_hex_str_json(chain_id: ChainId) -> Result<serde_json::Value, Error> {
    let chain_id: ethers::core::types::U64 = chain_id.into();
    to_value(chain_id)
}

fn to_value(val: impl Serialize) -> Result<serde_json::Value, Error> {
    serde_json::to_value(val).map_err(|_err| Error::Fatal {
        error: "Failed to serialize json value".into(),
    })
}

fn dapp_transaction_result_error(
    mut partial_result: DappTransactionResult,
    err: Error,
) -> Option<DappTransactionResult> {
    partial_result.error_message = Some(err.message_for_ui_callback());
    Some(partial_result)
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
    ParseError = -32700,
    InvalidRequest = -32600,
    MethodNotFound = -32601,
    InvalidParams = -32602,
    InternalError = -32603,

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

// More tests are in integrations tests in the [dev server.](tools/dev-server/static/ethereum.html)
#[cfg(test)]
mod tests {
    use anyhow::Result;
    use ethers::types::{Address, TransactionRequest, U256};
    use jsonrpsee::types::{Id, RequestSer, Response};
    use strum::IntoEnumIterator;

    use super::*;
    use crate::{
        app_core::tests::{InPageRequestContextMockArgs, TmpCore},
        protocols::eth::{
            in_page_provider::{
                in_page_request::{
                    AddEthereumChainParameter, InPageRequest, InPageRequestParams,
                },
                load_in_page_provider_script,
            },
            ChainId,
        },
        utils::new_uuid,
    };

    impl DappKeyProvider {
        /// `call("method_name", rpc_params!["arg1", "arg2"])`
        fn test_call(self, request: InPageRequest) -> Result<()> {
            let id = Id::Str(new_uuid().into());
            let InPageRequestParams { method, params } = request.try_into()?;
            let request = RequestSer::owned(id, method, Some(params));
            let raw_request =
                serde_json::to_string(&request).expect("request serializes");
            let handle = self.in_page_request(raw_request);
            rt::block_on(handle)??;
            Ok(())
        }
    }

    fn authorize_dapp(core: &TmpCore) -> Result<String> {
        let provider = core.in_page_provider();
        provider.test_call(InPageRequest::EthAccounts(()))?;
        core.wait_for_first_in_page_response();
        let responses = core.responses();
        let response = responses.first().unwrap();
        let response: Response<Vec<String>> = serde_json::from_str(response).unwrap();
        Ok(response.result.into_iter().next().unwrap())
    }

    fn check_dapp_authorization(core: &TmpCore) {
        assert!(core.dapp_approval().is_some());
        let responses = core.responses();
        assert_eq!(responses.len(), 1);
        assert_eq!(core.notifications().len(), 1);
        assert!(!responses[0].to_lowercase().contains("error"));
    }

    fn check_dapp_authorization_and_dapp_allotment(core: &TmpCore) {
        check_dapp_authorization(core);
        core.wait_for_ui_callbacks(1);
        let dapp_allotment_results = core.dapp_allotment_transfer_results();
        assert_eq!(dapp_allotment_results.len(), 1);
        let dapp_host = core
            .dapp_url()
            .host()
            .expect("dapp url has host")
            .to_string();
        assert_eq!(dapp_allotment_results[0].dapp_identifier, dapp_host);
        assert!(dapp_allotment_results[0].error_message.is_none());
    }

    #[test]
    fn responds_on_allowed() -> Result<()> {
        let core = TmpCore::new()?;
        core.fund_first_profile_wallet(ChainId::default_dapp_chain(), 10)?;

        let _ = authorize_dapp(&core)?;
        core.wait_for_ui_callbacks(1);
        check_dapp_authorization_and_dapp_allotment(&core);

        Ok(())
    }

    #[test]
    fn missing_params_field_ok() -> Result<()> {
        let s = r#"{"jsonrpc":"2.0","id":"abcd","method":"eth_requestAccounts"}"#;
        let core = TmpCore::new()?;
        let _ = authorize_dapp(&core)?;
        let mock_args = InPageRequestContextMockArgs::builder()
            .user_approves(true)
            .transfer_allotment(false)
            .build();
        let provider = core.in_page_provider_with_args(mock_args);
        let res = rt::block_on(provider.raw_json_rpc_request(s.into()))?;
        assert!(res.unwrap().success);
        Ok(())
    }

    #[test]
    fn responds_on_invalid_method() -> Result<()> {
        let s = r#"{"jsonrpc":"2.0","id":"abcd","method":"fooBar","params": ["foo"]}"#;
        let core = TmpCore::new()?;
        let provider = core.in_page_provider();
        let res = rt::block_on(provider.raw_json_rpc_request(s.into()))?.unwrap();
        let expected_code = InPageErrorCode::MethodNotFound.to_i32().to_string();
        assert!(res.result.contains(&expected_code));
        Ok(())
    }

    #[test]
    fn responds_on_invalid_params() -> Result<()> {
        let s = r#"{"jsonrpc":"2.0","id":"abcd","method":"eth_requestAccounts","params": ["foo"]}"#;
        let core = TmpCore::new()?;
        let provider = core.in_page_provider();
        let res = rt::block_on(provider.raw_json_rpc_request(s.into()))?.unwrap();
        let expected_code = InPageErrorCode::InvalidParams.to_i32().to_string();
        assert!(res.result.contains(&expected_code));
        Ok(())
    }

    #[test]
    fn respects_no_transfer_allotment() -> Result<()> {
        let core = TmpCore::new()?;
        let mock_args = InPageRequestContextMockArgs::builder()
            .user_approves(true)
            .transfer_allotment(false)
            .build();
        let provider = core.in_page_provider_with_args(mock_args);
        provider.test_call(InPageRequest::EthAccounts(()))?;
        core.wait_for_first_in_page_response();

        check_dapp_authorization(&core);

        let dapp_allotment_results = core.dapp_allotment_transfer_results();
        assert_eq!(dapp_allotment_results.len(), 0);

        Ok(())
    }

    #[test]
    fn responds_on_transfer_allotment_error() -> Result<()> {
        let core = TmpCore::new()?;

        let _ = authorize_dapp(&core)?;

        check_dapp_authorization(&core);
        core.wait_for_ui_callbacks(1);

        let dapp_allotment_results = core.dapp_allotment_transfer_results();
        assert_eq!(dapp_allotment_results.len(), 1);
        let error_message = dapp_allotment_results[0].error_message.as_ref().unwrap();
        assert!(error_message.to_lowercase().contains("funds"));

        Ok(())
    }

    #[test]
    fn responds_on_user_reject() -> Result<()> {
        let core = TmpCore::new()?;
        let mock_args = InPageRequestContextMockArgs::builder()
            .user_approves(false)
            .build();
        let provider = core.in_page_provider_with_args(mock_args);
        provider.test_call(InPageRequest::EthAccounts(()))?;
        core.wait_for_first_in_page_response();

        assert!(core.dapp_approval().is_some());
        let responses = core.responses();
        assert_eq!(responses.len(), 1);
        core.wait_for_ui_callbacks(1);
        let dapp_allotment_results = core.dapp_allotment_transfer_results();
        assert_eq!(dapp_allotment_results.len(), 0);

        let user_rejected = InPageErrorCode::UserRejected.to_i32().to_string();
        assert!(responses[0].contains(&user_rejected));

        Ok(())
    }

    #[test]
    fn disallows_un_approved() -> Result<()> {
        let core = TmpCore::new()?;

        let mock_args = InPageRequestContextMockArgs::builder()
            .user_approves(false)
            .build();
        let provider = core.in_page_provider_with_args(mock_args);
        provider.test_call(InPageRequest::PersonalSign(
            "0xabcd1234".parse()?,
            "0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826".parse()?,
            None,
        ))?;

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

        let _ = authorize_dapp(&core)?;

        // This request should be refused as it's an unsupported method
        let provider = core.in_page_provider();
        provider.test_call(InPageRequest::EthSign(
            "0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826".parse()?,
            "0xabcd1234".parse()?,
        ))?;

        let responses = core.responses();
        assert!(core.dapp_approval().is_some());
        assert_eq!(responses.len(), 2);

        let unsupported = InPageErrorCode::UnsupportedMethod.to_i32().to_string();
        assert!(responses[1].contains(&unsupported));

        Ok(())
    }

    #[test]
    fn personal_sign_callback() -> Result<()> {
        let core = TmpCore::new()?;

        let address = authorize_dapp(&core)?;

        let provider = core.in_page_provider();
        provider.test_call(InPageRequest::PersonalSign(
            "0xabcd".parse()?,
            address.parse()?,
            None,
        ))?;
        // Dapp allotment transfer + personal sign approved
        core.wait_for_ui_callbacks(2);

        let responses = core.responses();
        assert!(core.dapp_approval().is_some());
        assert_eq!(responses.len(), 2);
        assert_eq!(core.dapp_signature_results().len(), 1);

        Ok(())
    }

    #[test]
    fn send_transactions_callback() -> Result<()> {
        let core = TmpCore::new()?;
        core.fund_first_profile_wallet(ChainId::default_dapp_chain(), 10)?;

        let dapp_address = authorize_dapp(&core)?;
        let dapp_address: Address = dapp_address.parse().expect("checksum address");

        let tx = TransactionRequest::new()
            .to(Address::random())
            .value(U256::one())
            .from(dapp_address);

        let provider = core.in_page_provider();
        provider.test_call(InPageRequest::EthSendTransaction(tx))?;
        // Dapp allotment transfer + tx approved + tx succeeded
        core.wait_for_ui_callbacks(3);

        let approval_results = core.dapp_tx_approvals();
        let tx_results = core.dapp_tx_results();

        assert_eq!(approval_results.len(), 1);
        assert_eq!(tx_results.len(), 1);
        assert!(tx_results[0].explorer_url.is_some());
        assert!(tx_results[0].error_message.is_none());

        Ok(())
    }

    #[test]
    fn send_transactions_error_callback() -> Result<()> {
        let core = TmpCore::new()?;

        let dapp_address = authorize_dapp(&core)?;
        let dapp_address: Address = dapp_address.parse().expect("checksum address");

        let tx = TransactionRequest::new()
            .to(Address::random())
            .value(U256::one())
            .from(dapp_address);

        let provider = core.in_page_provider();
        provider.test_call(InPageRequest::EthSendTransaction(tx))?;
        // Dapp allotment transfer + tx approved + tx error
        core.wait_for_ui_callbacks(3);

        let approval_results = core.dapp_tx_approvals();
        let tx_results = core.dapp_tx_results();

        assert_eq!(approval_results.len(), 1);
        assert_eq!(tx_results.len(), 1);
        assert!(tx_results[0].explorer_url.is_none());
        assert!(tx_results[0].error_message.is_some());

        Ok(())
    }

    #[test]
    fn proxied_method_ok() -> Result<()> {
        let core = TmpCore::new()?;

        let _ = authorize_dapp(&core)?;

        let provider = core.in_page_provider();
        provider.test_call(InPageRequest::EthGasPrice(()))?;

        let responses = core.responses();
        assert_eq!(responses.len(), 2);

        Ok(())
    }

    #[test]
    fn add_ethereum_chain() -> Result<()> {
        let core = TmpCore::new()?;

        let _ = authorize_dapp(&core)?;

        let provider = core.in_page_provider();
        provider.test_call(InPageRequest::WalletAddEthereumChain(
            AddEthereumChainParameter {
                chain_id: "0x1".to_string(),
            },
        ))?;

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

        let network_version = ChainId::default_dapp_chain().network_version();
        let chain_id = ChainId::default_dapp_chain().display_hex();

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
