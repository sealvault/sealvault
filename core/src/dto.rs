// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashSet, iter, ops::Sub, sync::Arc};

use futures::StreamExt;
use lazy_static::lazy_static;
use regex::Regex;
use strum::IntoEnumIterator;
use typed_builder::TypedBuilder;
use url::Url;

/// Data transfer objects passed through FFI to host languages.
use crate::db::{models as m, ConnectionPool, DeferredTxConnection, DeterministicId};
use crate::{
    async_runtime as rt, config,
    favicon::{fetch_favicons, warm_favicons_cache},
    http_client::HttpClient,
    protocols::{eth, eth::ankr, FungibleTokenType},
    resources::CoreResourcesI,
    Error,
};

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreProfile {
    pub id: String,
    pub name: String,
    pub picture: Vec<u8>,
    pub wallets: Vec<CoreAddress>,
    pub dapps: Vec<CoreDapp>,
    pub created_at: String,
    pub updated_at: Option<String>,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreDapp {
    pub id: String,
    pub profile_id: String,
    pub human_identifier: String,
    pub url: String,
    pub addresses: Vec<CoreAddress>,
    /// The selected address for the dapp
    pub selected_address_id: Option<String>,
    pub favicon: Option<Vec<u8>>,
    pub last_used: Option<String>,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreAddress {
    pub id: String,
    pub is_wallet: bool,
    pub checksum_address: String,
    pub blockchain_explorer_link: String,
    pub chain_display_name: String,
    pub is_test_net: bool,
    pub chain_icon: Vec<u8>,
    pub native_token: CoreFungibleToken,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreFungibleToken {
    pub id: String,
    pub symbol: String,
    pub amount: Option<String>,
    pub token_type: FungibleTokenType,
    pub icon: Option<Vec<u8>>,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreNFT {
    pub id: String,
    pub display_name: String,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreTokens {
    pub address_id: String,
    pub native_token: CoreFungibleToken,
    pub fungible_tokens: Vec<CoreFungibleToken>,
    pub nfts: Vec<CoreNFT>,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreEthChain {
    /// Ethereum chain id.
    /// Not using db ids here, because Ethereum chains are lazy-inserted into the DB, so not all
    /// addable chains will have a DB id yet.
    #[builder(setter(into))]
    pub chain_id: u64,
    #[builder(setter(into))]
    pub display_name: String,
}

/// Errors passed to the UI.
/// Fallible functions exposed through FFI should use this error type by default.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CoreError {
    /// The operation resulted in an error, but it can be retried.
    #[error("Retriable Error: '{error}'")]
    Retriable { error: String },
    /// The user should be prompted to restart the application.
    #[error("Fatal Error: '{error}'")]
    Fatal { error: String },
    // An error where the message can be presented to the user directly.
    #[error("{explanation}")]
    User { explanation: String },
}

#[derive(Debug)]
pub struct Assembler {
    resources: Arc<dyn CoreResourcesI>,
}

impl Assembler {
    pub fn new(resources: Arc<dyn CoreResourcesI>) -> Self {
        Self { resources }
    }

    fn connection_pool(&self) -> &ConnectionPool {
        self.resources.connection_pool()
    }

    fn http_client(&self) -> &HttpClient {
        self.resources.http_client()
    }

    fn rpc_manager(&self) -> &dyn eth::RpcManagerI {
        self.resources.rpc_manager()
    }

    /// Combine data from multiple sources to create Profile data transfer objects.
    /// If `fetch_dapp_icons` is true, it fetches favicons for dapps which makes this function do
    /// blocking network requests. If it's false the favicons are still fetched in the background,
    /// but not returned so that the on the next invocation of the function they are returned from
    /// cache.
    pub fn assemble_profiles(
        &self,
        fetch_dapp_icons: bool,
    ) -> Result<Vec<CoreProfile>, Error> {
        // Important to pass down connection to make sure we see a consistent view of the db.
        self.connection_pool().deferred_transaction(|mut tx_conn| {
            let mut profiles: Vec<CoreProfile> = Default::default();
            for profile in m::Profile::list_all(tx_conn.as_mut())? {
                let m::Profile {
                    deterministic_id,
                    name,
                    picture_id,
                    created_at,
                    updated_at,
                    ..
                } = profile;

                let dapps = self.assemble_dapps(
                    &mut tx_conn,
                    &deterministic_id,
                    fetch_dapp_icons,
                )?;
                let wallets = self.assemble_wallets(&mut tx_conn, &deterministic_id)?;
                let picture =
                    m::ProfilePicture::fetch_image(tx_conn.as_mut(), &picture_id)?;

                let profile = CoreProfile::builder()
                    .id(deterministic_id.into())
                    .name(name)
                    .picture(picture)
                    .wallets(wallets)
                    .dapps(dapps)
                    .created_at(created_at)
                    .updated_at(updated_at)
                    .build();

                profiles.push(profile);
            }
            Ok(profiles)
        })
    }

    fn assemble_wallets(
        &self,
        tx_conn: &mut DeferredTxConnection,
        profile_id: &DeterministicId,
    ) -> Result<Vec<CoreAddress>, Error> {
        let addresses = m::Address::list_profile_wallets(tx_conn.as_mut(), profile_id)?;
        let mut results: Vec<CoreAddress> = Default::default();
        for address in addresses {
            let address = self.assemble_address_inner(tx_conn, address)?;
            results.push(address);
        }
        Ok(results)
    }

    fn assemble_dapps(
        &self,
        tx_conn: &mut DeferredTxConnection,
        profile_id: &DeterministicId,
        fetch_dapp_icons: bool,
    ) -> Result<Vec<CoreDapp>, Error> {
        let dapps = m::Dapp::list_for_profile(tx_conn.as_mut(), profile_id)?;
        let urls: Vec<Url> = dapps.iter().map(|d| d.url.clone().into()).collect();
        let favicons = if fetch_dapp_icons {
            fetch_favicons(self.http_client(), urls)
        } else {
            warm_favicons_cache(self.http_client().clone(), urls)
        }?;
        let mut results: Vec<CoreDapp> = Default::default();
        for (dapp, icon) in dapps.into_iter().zip(favicons) {
            let dapp = self.assemble_dapp(tx_conn, profile_id, dapp, icon)?;
            results.push(dapp);
        }
        Ok(results)
    }

    fn assemble_dapp(
        &self,
        tx_conn: &mut DeferredTxConnection,
        profile_id: &DeterministicId,
        dapp: m::Dapp,
        favicon: Option<Vec<u8>>,
    ) -> Result<CoreDapp, Error> {
        let params = m::ListAddressesForDappParams::builder()
            .profile_id(profile_id)
            .dapp_id(&dapp.deterministic_id)
            .build();
        let addresses = m::Address::list_for_dapp(tx_conn.as_mut(), &params)?;

        let mut core_addresses: Vec<CoreAddress> = Default::default();
        for address in addresses.into_iter() {
            let address = self.assemble_address_inner(tx_conn, address)?;
            core_addresses.push(address)
        }

        let dapp_session_params = m::FetchDappSessionParams::builder()
            .dapp_id(&dapp.deterministic_id)
            .profile_id(profile_id)
            .build();
        let dapp_session =
            m::LocalDappSession::fetch_eth_session(tx_conn, &dapp_session_params)?;
        let selected_address_id: Option<String> =
            dapp_session.map(|s| s.address_id.into());

        let m::Dapp {
            deterministic_id,
            identifier,
            url,
            ..
        } = dapp;
        let result = CoreDapp::builder()
            .id(deterministic_id.into())
            .profile_id(profile_id.clone().into())
            .human_identifier(identifier)
            .url((&url).into())
            .addresses(core_addresses)
            .selected_address_id(selected_address_id)
            .favicon(favicon)
            // TODO move last used at from local sessions to dapp
            .last_used(None)
            .build();
        Ok(result)
    }

    fn chain_id_for_address(
        &self,
        tx_conn: &mut DeferredTxConnection,
        address: &m::Address,
    ) -> Result<eth::ChainId, Error> {
        let chain_id = m::Chain::fetch_eth_chain_id(tx_conn.as_mut(), &address.chain_id)?;
        Ok(chain_id)
    }

    pub fn assemble_address(
        &self,
        address_id: &m::AddressId,
    ) -> Result<CoreAddress, Error> {
        let result = self.connection_pool().deferred_transaction(|mut tx_conn| {
            let address = m::Address::fetch(tx_conn.as_mut(), address_id)?;
            self.assemble_address_inner(&mut tx_conn, address)
        })?;
        Ok(result)
    }

    fn assemble_address_inner(
        &self,
        tx_conn: &mut DeferredTxConnection,
        address: m::Address,
    ) -> Result<CoreAddress, Error> {
        let chain_id = self.chain_id_for_address(tx_conn, &address)?;

        let m::Address {
            deterministic_id,
            address,
            ..
        } = address;

        // We send the native token without balance first to return result ASAP.
        // UI then fetches balance async.
        let native_token = self.make_native_token(address, chain_id, None)?;

        let is_wallet =
            m::Address::is_profile_wallet(tx_conn.as_mut(), &deterministic_id)?;

        let chain_icon = chain_id.native_token().icon()?;
        let explorer_link: String = eth::explorer::address_url(chain_id, address)?.into();
        let result = CoreAddress::builder()
            .id(deterministic_id.into())
            .is_wallet(is_wallet)
            .checksum_address(address.to_string())
            .blockchain_explorer_link(explorer_link)
            .chain_display_name(chain_id.display_name())
            .is_test_net(chain_id.is_test_net())
            .chain_icon(chain_icon)
            .native_token(native_token)
            .build();

        Ok(result)
    }

    /// Fetch all the tokens for an address id.
    pub fn tokens_for_address_id(
        &self,
        address_id: m::AddressId,
    ) -> Result<CoreTokens, Error> {
        let mut conn = self.connection_pool().connection()?;
        let address = m::Address::fetch_address(&mut conn, &address_id)?;
        let mut tokens = self.tokens_for_address(address)?;
        let address_id: &str = address_id.as_ref();
        tokens.retain(|t| t.address_id == address_id);
        if tokens.len() == 1 {
            Ok(tokens
                .into_iter()
                .next()
                .expect("checked that tokens has one element"))
        } else {
            Err(Error::Retriable {
                error: "Failed to fetch tokens for address id.".into(),
            })
        }
    }

    /// Fetch all the tokens for an address id.
    pub fn tokens_for_address(
        &self,
        address: eth::ChecksumAddress,
    ) -> Result<Vec<CoreTokens>, Error> {
        self.assemble_tokens(address).or_else(|error| {
            log::error!("Error fetching tokens from Ankr API: '{error}'");
            // Fall back to just fetching native token
            self.assemble_native_tokens(address)
        })
    }

    fn assemble_native_tokens(
        &self,
        address: eth::ChecksumAddress,
    ) -> Result<Vec<CoreTokens>, Error> {
        let mut conn = self.connection_pool().connection()?;
        let chain_ids = m::Address::fetch_eth_chains_for_address(&mut conn, address)?;
        let token_balances = rt::block_on(self.fetch_native_tokens(address, chain_ids))?;
        let results = self.connection_pool().deferred_transaction(|mut tx_conn| {
            let results = token_balances
                .into_iter()
                .map(|balance| {
                    let address_id = m::Address::fetch_or_create_id_by_address_on_chain(
                        &mut tx_conn,
                        address,
                        balance.chain_id,
                    )?
                    .ok_or_else(|| Error::Fatal {
                        // Not part of the same transaction to avoid accidentally locking the DB while
                        // waiting for the request.
                        error: "Address id must exist since it was just fetched from DB."
                            .into(),
                    })?;
                    let native_token = self.make_native_token(
                        address,
                        balance.chain_id,
                        Some(balance.display_amount()),
                    )?;
                    Ok(CoreTokens::builder()
                        .address_id(address_id.to_string())
                        .native_token(native_token)
                        .fungible_tokens(Default::default())
                        .nfts(Default::default())
                        .build())
                })
                .collect::<Vec<Result<CoreTokens, Error>>>();
            Ok(results)
        })?;

        results.into_iter().collect()
    }

    async fn fetch_native_tokens<I>(
        &self,
        address: eth::ChecksumAddress,
        chain_ids: I,
    ) -> Result<Vec<eth::NativeTokenAmount>, Error>
    where
        I: IntoIterator<Item = eth::ChainId>,
    {
        let results: Vec<Result<eth::NativeTokenAmount, Error>> =
            futures::stream::iter(chain_ids)
                .map(|chain_id| self.fetch_native_token(address, chain_id))
                .buffered(config::MAX_ASYNC_CONCURRENT_REQUESTS)
                .collect()
                .await;
        results.into_iter().collect()
    }

    async fn fetch_native_token(
        &self,
        address: eth::ChecksumAddress,
        chain_id: eth::ChainId,
    ) -> Result<eth::NativeTokenAmount, Error> {
        let provider = self.rpc_manager().eth_api_provider(chain_id);
        let balance = provider.native_token_balance_async(address).await?;
        Ok(balance)
    }

    fn make_native_token(
        &self,
        address: eth::ChecksumAddress,
        chain_id: eth::ChainId,
        amount: Option<String>,
    ) -> Result<CoreFungibleToken, Error> {
        let native_token_id = format!("eth-{chain_id}-{address}");
        let icon = Some(chain_id.native_token().icon()?);
        let native_token = CoreFungibleToken::builder()
            .id(native_token_id)
            .symbol(chain_id.native_token().to_string())
            .amount(amount)
            .token_type(FungibleTokenType::Native)
            .icon(icon)
            .build();
        Ok(native_token)
    }

    fn assemble_fungible_tokens(
        &self,
        tokens: Vec<eth::FungibleTokenBalance>,
    ) -> Result<Vec<CoreFungibleToken>, Error> {
        let (tokens_with_logo, tokens_no_logo): (Vec<_>, Vec<_>) =
            tokens.into_iter().partition(|token| token.logo.is_some());

        let logo_urls = tokens_with_logo
            .iter()
            .map(|token| token.logo.clone().expect("tokens with logo have logo"));
        let maybe_icons = rt::block_on(self.http_client().get_bytes(logo_urls));
        let icons_for_all = maybe_icons
            .into_iter()
            .chain(iter::repeat(None).take(tokens_no_logo.len()));

        let result: Result<Vec<CoreFungibleToken>, Error> = tokens_with_logo
            .into_iter()
            .chain(tokens_no_logo)
            .zip(icons_for_all)
            .map(|(token, icon)| {
                let amount = token.display_amount();
                let eth::FungibleTokenBalance {
                    contract_address,
                    symbol,
                    ..
                } = token;
                Ok(CoreFungibleToken::builder()
                    // The id being the contract address is relied on in the core
                    // `eth_transfer_fungible_token` interface.
                    .id(contract_address.to_string())
                    .symbol(symbol)
                    .amount(Some(amount))
                    .token_type(FungibleTokenType::Custom)
                    .icon(icon)
                    .build())
            })
            .collect();
        result
    }

    fn assemble_nfts(&self, tokens: Vec<eth::NFTBalance>) -> Vec<CoreNFT> {
        tokens
            .into_iter()
            .map(|token| {
                let eth::NFTBalance {
                    chain_id,
                    contract_address,
                    name,
                    token_id,
                    ..
                } = token;
                let id = format!("{chain_id}-{contract_address}-{token_id}");
                CoreNFT::builder().id(id).display_name(name).build()
            })
            .collect()
    }

    fn assemble_tokens(
        &self,
        address: eth::ChecksumAddress,
    ) -> Result<Vec<CoreTokens>, Error> {
        use ankr::AnkrRpcI;
        let ankr_api = ankr::AnkrRpc::new()?;
        let token_balances = rt::block_on(ankr_api.get_token_balances(address))?;

        self.connection_pool().deferred_transaction(|mut tx_conn| {
            let mut results: Vec<CoreTokens> = Default::default();
            let mut chains_from_api: HashSet<eth::ChainId> = Default::default();

            for balances in token_balances.into_iter() {
                let address_id = m::Address::fetch_or_create_id_by_address_on_chain(
                    &mut tx_conn,
                    address,
                    balances.chain_id,
                )?
                .ok_or_else(|| Error::Fatal {
                    error: "Assumed address is already in the DB".into(),
                })?;

                // Update DB from remote API
                m::Token::upsert_tokens(&mut tx_conn, &balances, &address_id)?;

                let eth::TokenBalances {
                    chain_id,
                    native_token,
                    fungible_tokens,
                    nfts,
                    ..
                } = balances;
                chains_from_api.insert(chain_id);
                let native_token = self.make_native_token(
                    address,
                    chain_id,
                    Some(native_token.display_amount()),
                )?;
                let fungible_tokens = self.assemble_fungible_tokens(fungible_tokens)?;
                let nfts = self.assemble_nfts(nfts);

                results.push(
                    CoreTokens::builder()
                        .address_id(address_id.to_string())
                        .native_token(native_token)
                        .fungible_tokens(fungible_tokens)
                        .nfts(nfts)
                        .build(),
                )
            }

            // If an address doesn't have any tokens, Ankr API won't return a result for it, but we
            // still want to display a 0 balance for the native token if the address is in the DB.
            let existing_chains: HashSet<eth::ChainId> =
                m::Address::fetch_eth_chains_for_address(tx_conn.as_mut(), address)?
                    .into_iter()
                    .collect();

            for chain_id in existing_chains.sub(&chains_from_api) {
                let native_token =
                    self.make_native_token(address, chain_id, Some("0".into()))?;
                let address_id = m::Address::fetch_or_create_id_by_address_on_chain(
                    &mut tx_conn,
                    address,
                    chain_id,
                )?;
                if let Some(address_id) = address_id {
                    results.push(
                        CoreTokens::builder()
                            .address_id(address_id.to_string())
                            .native_token(native_token)
                            .fungible_tokens(Default::default())
                            .nfts(Default::default())
                            .build(),
                    )
                }
            }
            Ok(results)
        })
    }

    /// List supported Ethereum chains
    pub fn list_eth_chains(&self) -> Vec<CoreEthChain> {
        eth::ChainId::iter()
            .map(|chain_id| {
                let display_name = chain_id.display_name();
                CoreEthChain::builder()
                    .chain_id(chain_id)
                    .display_name(display_name)
                    .build()
            })
            .collect()
    }
}

lazy_static! {
    // Hack to get errors that should be displayed to users.
    static ref JSONRPC_USER_ERROR_REGEX: Regex =
        Regex::new(r"funds|gas|underpriced").expect("static is ok");
}

impl From<Error> for CoreError {
    fn from(err: Error) -> Self {
        match err {
            Error::Fatal { error } => CoreError::Fatal { error },
            Error::User { explanation } => CoreError::User { explanation },
            Error::Retriable { error } => CoreError::Retriable { error },
            Error::JsonRpc { code, message } => {
                if JSONRPC_USER_ERROR_REGEX.is_match(&message) {
                    CoreError::User {
                        explanation: message,
                    }
                } else {
                    CoreError::Retriable {
                        error: format!("JSON-RPC error {} message '{}'", code, message),
                    }
                }
            }
        }
    }
}
