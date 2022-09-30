// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::async_runtime as rt;
use crate::db::models::ListAddressesForDappParams;
/// Data transfer objects passed through FFI to host languages.
use crate::db::{models as m, DeferredTxConnection};
use crate::favicon::fetch_favicons;
use crate::http_client::{GetAllBytes, HttpClient, HttpClientError};
use crate::protocols::eth::ankr;
use crate::protocols::{eth, TokenType};
use crate::Error;
use std::collections::HashMap;
use std::iter;
use typed_builder::TypedBuilder;
use url::Url;

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
    pub chain_icon: Vec<u8>,
    pub native_token: CoreToken
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct CoreToken {
    pub id: String,
    pub symbol: String,
    pub amount: Option<String>,
    pub token_type: TokenType,
    pub icon: Option<Vec<u8>>,
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
    /// Errors that user can make and we want to want to explain to them what's wrong.
    /// The explanation can be presented directly to the user.
    #[error("{explanation}")]
    User { explanation: String },
}

impl From<Error> for CoreError {
    fn from(err: Error) -> Self {
        match err {
            Error::Fatal { error } => CoreError::Fatal { error },
            Error::User { explanation } => CoreError::User { explanation },
            Error::Retriable { error } => CoreError::Retriable { error },
            Error::JsonRpc { code, message } => CoreError::Retriable {
                error: format!("JSON-RPC error {} message '{}'", code, message),
            },
        }
    }
}

#[derive(Debug)]
pub struct Assembler<'a> {
    eth_chains_by_db_id: HashMap<String, m::EthChain>,
    http_client: &'a HttpClient,
    rpc_manager: &'a dyn eth::RpcManagerI,
    tx_conn: DeferredTxConnection<'a>,
}

impl<'a> Assembler<'a> {
    pub fn init(
        http_client: &'a HttpClient,
        rpc_manager: &'a dyn eth::RpcManagerI,
        mut tx_conn: DeferredTxConnection<'a>,
    ) -> Result<Self, Error> {
        let eth_chains = m::Chain::list_eth_chains(tx_conn.as_mut())?;
        let eth_chains_by_db_id: HashMap<String, m::EthChain> = eth_chains
            .into_iter()
            .map(|c| (c.db_id.clone(), c))
            .collect();

        Ok(Self {
            eth_chains_by_db_id,
            http_client,
            rpc_manager,
            tx_conn,
        })
    }

    /// Combine data from multiple sources to create Account data transfer objects.
    pub fn assemble_accounts(&mut self) -> Result<Vec<CoreAccount>, Error> {
        let mut accounts: Vec<CoreAccount> = Default::default();
        for account in m::Account::list_all(self.tx_conn.as_mut())? {
            let m::Account {
                deterministic_id,
                name,
                picture_id,
                created_at,
                updated_at,
                ..
            } = account;

            let dapps = self.assemble_dapps(&deterministic_id)?;
            let wallets = self.assemble_wallets(&deterministic_id)?;
            let picture =
                m::AccountPicture::fetch_image(self.tx_conn.as_mut(), &picture_id)?;

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
    }

    fn assemble_wallets(&mut self, account_id: &str) -> Result<Vec<CoreAddress>, Error> {
        let addresses =
            m::Address::list_account_wallets(self.tx_conn.as_mut(), account_id)?;
        let mut results: Vec<CoreAddress> = Default::default();
        for address in addresses {
            let address = self.assemble_address(address, true)?;
            results.push(address);
        }
        Ok(results)
    }

    fn assemble_dapps(&mut self, account_id: &str) -> Result<Vec<CoreDapp>, Error> {
        let dapps = m::Dapp::list_for_account(self.tx_conn.as_mut(), account_id)?;
        let urls: Vec<Url> = dapps.iter().map(|d| d.url.clone().into()).collect();
        let favicons = fetch_favicons(self.http_client, urls)?;
        let mut results: Vec<CoreDapp> = Default::default();
        for (dapp, icon) in dapps.into_iter().zip(favicons) {
            let dapp = self.assemble_dapp(account_id, dapp, icon)?;
            results.push(dapp);
        }
        Ok(results)
    }

    fn assemble_dapp(
        &mut self,
        account_id: &str,
        dapp: m::Dapp,
        favicon: Option<Vec<u8>>,
    ) -> Result<CoreDapp, Error> {
        let params = ListAddressesForDappParams::builder()
            .account_id(account_id)
            .dapp_id(&dapp.deterministic_id)
            .build();
        let mut addresses: Vec<CoreAddress> = Default::default();
        for address in m::Address::list_for_dapp(self.tx_conn.as_mut(), &params)? {
            let address = self.assemble_address(address, false)?;
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

    fn chain_id_for_address(&self, address: &m::Address) -> Result<eth::ChainId, Error> {
        let chain = self
            .eth_chains_by_db_id
            .get(&*address.chain_id)
            .ok_or(Error::Fatal {
                error: format!("Unknown chain db id: {}", &*address.chain_id),
            })?;
        Ok(chain.chain_id)
    }

    fn assemble_address(
        &self,
        address: m::Address,
        is_wallet: bool,
    ) -> Result<CoreAddress, Error> {
        let chain_id = self.chain_id_for_address(&address)?;

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
            .chain_icon(chain_icon)
            .native_token(native_token)
            .build();

        Ok(result)
    }

    pub fn native_token_for_address(&mut self, address_id: &str) -> Result<CoreToken, Error> {
        let address = m::Address::fetch(self.tx_conn.as_mut(), address_id)?;
        let chain_id = self.chain_id_for_address(&address)?;
        self.assemble_native_token(&address.address, chain_id)
    }

    fn native_token_without_balance(&self, address: &str, chain_id: eth::ChainId) -> Result<CoreToken, Error> {
        let native_token_id = format!("eth-{}-{}", chain_id,  address);
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
        let provider = self.rpc_manager.eth_api_provider(chain_id);
        let balance = provider.native_token_balance(address)?;
        native_token.amount = Some(balance.display_amount());
        Ok(native_token)
    }

    pub fn fungible_tokens_for_address(&mut self, address_id: &str) -> Result<Vec<CoreToken>, Error> {
        let address = m::Address::fetch(self.tx_conn.as_mut(), address_id)?;
        let chain_id = self.chain_id_for_address(&address)?;
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
        let icons = self.http_client.get_bytes(logo_urls)?;
        let mut maybe_icons: Vec<Option<Vec<u8>>> =
            Vec::with_capacity(tokens_with_logo.len());
        for icon_res in icons {
            match icon_res {
                Ok(icon) => maybe_icons.push(Some(icon)),
                Err(HttpClientError::Request { error }) => {
                    // Icon request errors are not sensitive, ok to log.
                    log::error!("Failed to fetch icon for fungible token with request error: {:?}", error);
                    maybe_icons.push(None);
                }
                Err(HttpClientError::Middleware { error }) => {
                    log::error!("Failed to fetch icon for fungible token with middleware error: {:?}", error);
                    maybe_icons.push(None);
                }
                Err(HttpClientError::Core { error }) => Err(error)?,
            }
        }
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
}
