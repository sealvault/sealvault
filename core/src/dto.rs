// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{iter, sync::Arc};

use lazy_static::lazy_static;
use regex::Regex;
use strum::IntoEnumIterator;
use typed_builder::TypedBuilder;
use url::Url;

/// Data transfer objects passed through FFI to host languages.
use crate::db::{models as m, ConnectionPool, DeferredTxConnection};
use crate::{
    async_runtime as rt,
    db::models::ListAddressesForDappParams,
    favicon::fetch_favicons,
    http_client::HttpClient,
    protocols::{eth, eth::ankr, TokenType},
    resources::{CoreResources, CoreResourcesI},
    Error,
};

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreAccount {
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
    pub human_identifier: String,
    pub url: String,
    pub addresses: Vec<CoreAddress>,
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
    pub native_token: CoreToken,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreToken {
    pub id: String,
    pub symbol: String,
    pub amount: Option<String>,
    pub token_type: TokenType,
    pub icon: Option<Vec<u8>>,
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
/// Fallible functions exposed through FFI should use this error type.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
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

    /// Combine data from multiple sources to create Account data transfer objects.
    pub fn assemble_accounts(&self) -> Result<Vec<CoreAccount>, Error> {
        // Important to pass down connection to make sure we see a consistent view of the db.
        self.connection_pool().deferred_transaction(|mut tx_conn| {
            let mut accounts: Vec<CoreAccount> = Default::default();
            for account in m::Account::list_all(tx_conn.as_mut())? {
                let m::Account {
                    deterministic_id,
                    name,
                    picture_id,
                    created_at,
                    updated_at,
                    ..
                } = account;

                let dapps = self.assemble_dapps(&mut tx_conn, &deterministic_id)?;
                let wallets = self.assemble_wallets(&mut tx_conn, &deterministic_id)?;
                let picture =
                    m::AccountPicture::fetch_image(tx_conn.as_mut(), &picture_id)?;

                let account = CoreAccount::builder()
                    .id(deterministic_id)
                    .name(name)
                    .picture(picture)
                    .wallets(wallets)
                    .dapps(dapps)
                    .created_at(created_at)
                    .updated_at(updated_at)
                    .build();

                accounts.push(account);
            }
            Ok(accounts)
        })
    }

    fn assemble_wallets(
        &self,
        tx_conn: &mut DeferredTxConnection,
        account_id: &str,
    ) -> Result<Vec<CoreAddress>, Error> {
        let addresses = m::Address::list_account_wallets(tx_conn.as_mut(), account_id)?;
        let mut results: Vec<CoreAddress> = Default::default();
        for address in addresses {
            let address = self.assemble_address(tx_conn, address, true)?;
            results.push(address);
        }
        Ok(results)
    }

    fn assemble_dapps(
        &self,
        tx_conn: &mut DeferredTxConnection,
        account_id: &str,
    ) -> Result<Vec<CoreDapp>, Error> {
        let dapps = m::Dapp::list_for_account(tx_conn.as_mut(), account_id)?;
        let urls: Vec<Url> = dapps.iter().map(|d| d.url.clone().into()).collect();
        let favicons = fetch_favicons(self.http_client(), urls)?;
        let mut results: Vec<CoreDapp> = Default::default();
        for (dapp, icon) in dapps.into_iter().zip(favicons) {
            let dapp = self.assemble_dapp(tx_conn, account_id, dapp, icon)?;
            results.push(dapp);
        }
        Ok(results)
    }

    fn assemble_dapp(
        &self,
        tx_conn: &mut DeferredTxConnection,
        account_id: &str,
        dapp: m::Dapp,
        favicon: Option<Vec<u8>>,
    ) -> Result<CoreDapp, Error> {
        let params = ListAddressesForDappParams::builder()
            .account_id(account_id)
            .dapp_id(&dapp.deterministic_id)
            .build();
        let mut addresses: Vec<CoreAddress> = Default::default();
        for address in m::Address::list_for_dapp(tx_conn.as_mut(), &params)? {
            let address = self.assemble_address(tx_conn, address, false)?;
            addresses.push(address)
        }
        let m::Dapp {
            deterministic_id,
            identifier,
            url,
            ..
        } = dapp;
        let result = CoreDapp::builder()
            .id(deterministic_id)
            .human_identifier(identifier)
            .url((&url).into())
            .addresses(addresses)
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

    fn assemble_address(
        &self,
        tx_conn: &mut DeferredTxConnection,
        address: m::Address,
        is_wallet: bool,
    ) -> Result<CoreAddress, Error> {
        let chain_id = self.chain_id_for_address(tx_conn, &address)?;

        let m::Address {
            deterministic_id,
            address,
            ..
        } = address;

        // We send the native token without balance first to return result ASAP.
        // UI then fetches balance async.
        let native_token = self.native_token_without_balance(&address, chain_id)?;

        let chain_icon = chain_id.native_token().icon()?;
        let explorer_link: String =
            eth::explorer::address_url(chain_id, &address)?.into();
        let result = CoreAddress::builder()
            .id(deterministic_id)
            .is_wallet(is_wallet)
            .checksum_address(address)
            .blockchain_explorer_link(explorer_link)
            .chain_display_name(chain_id.display_name())
            .is_test_net(chain_id.is_test_net())
            .chain_icon(chain_icon)
            .native_token(native_token)
            .build();

        Ok(result)
    }

    fn fetch_token_address(
        &self,
        address_id: &str,
    ) -> Result<(eth::ChainId, m::Address), Error> {
        self.connection_pool().deferred_transaction(|mut tx_conn| {
            let address = m::Address::fetch(tx_conn.as_mut(), address_id)?;
            let chain_id = self.chain_id_for_address(&mut tx_conn, &address)?;
            Ok((chain_id, address))
        })
    }

    pub fn native_token_for_address(&self, address_id: &str) -> Result<CoreToken, Error> {
        let (chain_id, address) = self.fetch_token_address(address_id)?;
        self.assemble_native_token(&address.address, chain_id)
    }

    fn native_token_without_balance(
        &self,
        address: &str,
        chain_id: eth::ChainId,
    ) -> Result<CoreToken, Error> {
        let native_token_id = format!("eth-{}-{}", chain_id, address);
        let icon = Some(chain_id.native_token().icon()?);
        let native_token = CoreToken::builder()
            .id(native_token_id)
            .symbol(chain_id.native_token().to_string())
            .amount(None)
            .token_type(TokenType::Native)
            .icon(icon)
            .build();
        Ok(native_token)
    }

    fn assemble_native_token(
        &self,
        address: &str,
        chain_id: eth::ChainId,
    ) -> Result<CoreToken, Error> {
        let mut native_token = self.native_token_without_balance(address, chain_id)?;
        let provider = self.rpc_manager().eth_api_provider(chain_id);
        let balance = provider.native_token_balance(address)?;
        native_token.amount = Some(balance.display_amount());
        Ok(native_token)
    }

    pub fn fungible_tokens_for_address(
        &self,
        address_id: &str,
    ) -> Result<Vec<CoreToken>, Error> {
        let (chain_id, address) = self.fetch_token_address(address_id)?;
        self.assemble_fungible_tokens(&address.address, chain_id)
    }

    fn assemble_fungible_tokens(
        &self,
        address: &str,
        chain_id: eth::ChainId,
    ) -> Result<Vec<CoreToken>, Error> {
        use ankr::AnkrRpcI;
        let ankr_api = ankr::AnkrRpc::new()?;
        let tokens_res = rt::block_on(ankr_api.get_account_balances(chain_id, address));
        let tokens: Vec<eth::FungibleTokenBalance> = match tokens_res {
            Ok(tokens) => Ok(tokens),
            Err(Error::Retriable { error }) => {
                log::error!(
                    "Retriable error fetching fungible token balances for address '{}': {}", address, error
                );
                Ok(Default::default())
            }
            Err(Error::JsonRpc { code, message }) => {
                log::error!(
                    "JSON-RPC error fetching fungible token balances for address '{}': {} {}", address, code, message
                );
                Ok(Default::default())
            }
            error => error,
        }?;

        let (tokens_with_logo, tokens_no_logo): (Vec<_>, Vec<_>) =
            tokens.into_iter().partition(|token| token.logo.is_some());

        let logo_urls = tokens_with_logo
            .iter()
            .map(|token| token.logo.clone().expect("tokens with logo have logo"));
        let maybe_icons = rt::block_on(self.http_client().get_bytes(logo_urls));
        let icons_for_all = maybe_icons
            .into_iter()
            .chain(iter::repeat(None).take(tokens_no_logo.len()));

        let result: Result<Vec<CoreToken>, Error> = tokens_with_logo
            .into_iter()
            .chain(tokens_no_logo)
            .zip(icons_for_all)
            .map(|(token, icon)| {
                let amount = token.display_amount();
                let contract_address = token.display_contract_address();
                let eth::FungibleTokenBalance { symbol, .. } = token;
                Ok(CoreToken::builder()
                    // The id being the contract address is relied on in the core
                    // `eth_transfer_fungible_token` interface.
                    .id(contract_address)
                    .symbol(symbol)
                    .amount(Some(amount))
                    .token_type(TokenType::Fungible)
                    .icon(icon)
                    .build())
            })
            .collect();
        result
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
