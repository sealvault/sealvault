// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::protocols::eth::token::FungibleTokenBalance;
use crate::protocols::eth::ChainId;
use crate::protocols::TokenType;
use crate::Error;
use ethers::types::{Address, U256};
use jsonrpsee::core::{async_trait, RpcResult};
use jsonrpsee::http_client::{HttpClient, HttpClientBuilder};
use jsonrpsee::proc_macros::rpc;
use jsonrpsee::types::error::{ErrorCode};
use serde::{Deserialize, Serialize};
use url::Url;

// Port number is important for, otherwise Jsonrpsee HTTP client doesn't work
const ANKR_API: &str = "https://rpc.ankr.com:443/multichain";
const PAGE_SIZE: usize = 100;

// The rpc macro adds the methods in this trait to the Jsonrpsee http client in this file.
// Server derive for tests.
#[rpc(client, server, namespace = "ankr")]
trait AnkrRpcApi {
    #[method(name = "getAccountBalance", param_kind = map)]
    async fn get_account_balance(
        &self,
        blockchain: Vec<AnkrBlockchain>,
        // Need to be camel case for correct generated code
        pageSize: usize,
        pageToken: Option<&str>,
        walletAddress: &str,
    ) -> RpcResult<AnkrTokenBalances>;
}

// The purpose of this trait is to let us mock the Ankr backend for tests
#[async_trait]
pub trait AnkrRpcI<'a> {
    fn client(&'a self) -> &'a HttpClient;

    /// Fetch account balances for an address on a chain from an Ankr advanced API.
    /// It's async to make it easy to fetch multiple addresses concurrently.
    async fn get_account_balances(
        &'a self,
        chain_id: ChainId,
        address: &str,
    ) -> Result<Vec<FungibleTokenBalance>, Error> {
        let mut page_token: Option<String> = None;
        let mut token_balances: Vec<AnkrTokenBalance> = Default::default();

        let ankr_chain_id = match chain_id {
            ChainId::EthMainnet => Ok(AnkrBlockchain::Eth),
            ChainId::PolygonMainnet => Ok(AnkrBlockchain::Polygon),
            _ => Err(Error::JsonRpc {
                code: ErrorCode::InvalidParams,
                message: format!("Chain {} is not supported for Ankr API", chain_id),
            }),
        }?;
        let blockchains: Vec<AnkrBlockchain> = vec![ankr_chain_id];

        loop {
            let result: AnkrTokenBalances = self
                .client()
                .get_account_balance(
                    blockchains.clone(),
                    PAGE_SIZE,
                    page_token.as_deref(),
                    address,
                )
                .await?;

            let AnkrTokenBalances {
                next_page_token,
                assets,
                ..
            } = result;
            token_balances.extend(assets);

            page_token = next_page_token;
            if page_token.is_none() {
                break;
            }
        }
        Ok(to_fungible_token_balances(token_balances))
    }
}

#[cfg(not(test))]
pub struct AnkrRpc {
    client: HttpClient,
}

#[cfg(not(test))]
impl AnkrRpc {
    pub fn new() -> Result<Self, Error> {
        let client = HttpClientBuilder::default()
            .build(ANKR_API)
            .map_err(|err| Error::Fatal {
                error: err.to_string(),
            })?;
        Ok(Self { client })
    }
}

#[cfg(not(test))]
impl<'a> AnkrRpcI<'a> for AnkrRpc {
    fn client(&'a self) -> &'a HttpClient {
        &self.client
    }
}

fn to_fungible_token_balances(
    ankr_balances: Vec<AnkrTokenBalance>,
) -> Vec<FungibleTokenBalance> {
    ankr_balances
        .into_iter()
        .filter_map(|b| match b.token_type {
            AnkrTokenType::Native => None,
            AnkrTokenType::Erc20 => {
                let token: Result<FungibleTokenBalance, Error> = b.try_into();
                match token {
                    Err(err) => {
                        log::error!("{:?}", err);
                        None
                    }
                    Ok(token) => Some(token),
                }
            }
        })
        .collect()
}

impl TryFrom<AnkrTokenBalance> for FungibleTokenBalance {
    type Error = Error;

    fn try_from(value: AnkrTokenBalance) -> Result<Self, Error> {
        if value.token_type != AnkrTokenType::Erc20 {
            return Err(Error::Retriable {
                error: format!(
                    "Invalid token type for fungible token: {}",
                    value.token_type
                ),
            });
        }
        let AnkrTokenBalance {
            contract_address,
            balance_raw_integer,
            token_decimals,
            blockchain,
            token_symbol,
            token_name,
            thumbnail,
            ..
        } = value;
        let contract_address = contract_address.ok_or_else(|| Error::Retriable {
            error: format!(
                "Missing contract address for ERC20 token '{}' on {} chain",
                token_symbol, blockchain
            ),
        })?;
        let amount =
            U256::from_dec_str(&balance_raw_integer).map_err(|_| Error::Retriable {
                error: format!(
                    "Invalid raw integer balance '{}' for token {} on chain {}",
                    balance_raw_integer, token_symbol, blockchain
                ),
            })?;
        let logo = Url::parse(&thumbnail).ok();
        Ok(Self {
            chain_id: blockchain.into(),
            contract_address,
            amount,
            decimals: token_decimals,
            symbol: token_symbol,
            name: token_name,
            logo,
        })
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnkrTokenBalances {
    total_balance_usd: String,
    assets: Vec<AnkrTokenBalance>,
    next_page_token: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnkrTokenBalance {
    blockchain: AnkrBlockchain,
    token_name: String,
    token_symbol: String,
    token_decimals: u8,
    token_type: AnkrTokenType,
    contract_address: Option<Address>,
    holder_address: Address,
    balance: String,
    balance_raw_integer: String,
    balance_usd: String,
    token_price: String,
    // Not URL, because it can empty string.
    thumbnail: String,
}

#[derive(
    Clone, Debug, Serialize, Deserialize, strum_macros::EnumString, strum_macros::Display,
)]
#[strum(serialize_all = "lowercase")]
#[serde(rename_all = "lowercase")]
pub enum AnkrBlockchain {
    Eth,
    Polygon,
}

impl From<AnkrBlockchain> for ChainId {
    fn from(value: AnkrBlockchain) -> Self {
        match value {
            AnkrBlockchain::Eth => ChainId::EthMainnet,
            AnkrBlockchain::Polygon => ChainId::PolygonMainnet,
        }
    }
}

#[derive(
    Debug,
    Eq,
    PartialEq,
    Serialize,
    Deserialize,
    strum_macros::EnumString,
    strum_macros::Display,
)]
#[strum(serialize_all = "UPPERCASE")]
#[serde(rename_all = "UPPERCASE")]
pub enum AnkrTokenType {
    Native,
    Erc20,
}

impl From<AnkrTokenType> for TokenType {
    fn from(value: AnkrTokenType) -> Self {
        match value {
            AnkrTokenType::Native => TokenType::Native,
            AnkrTokenType::Erc20 => TokenType::Fungible,
        }
    }
}

#[cfg(test)]
pub use tests::AnkrRpc;

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{async_runtime as rt};
    use jsonrpsee::core::logger::{Body, HttpLogger, MethodKind, Params, Request};
    use jsonrpsee::core::{async_trait, RpcResult};
    use jsonrpsee::http_client::{HttpClient, HttpClientBuilder};
    use jsonrpsee::http_server::{HttpServerBuilder, HttpServerHandle};
    use serde_json::json;
    use std::net::SocketAddr;
    use std::time::Instant;

    pub struct AnkrRpc {
        client: HttpClient,
        _sever_handle: HttpServerHandle,
    }

    impl AnkrRpc {
        pub fn new() -> Result<Self, Error> {
            let server = rt::block_on(
                HttpServerBuilder::default()
                    .custom_tokio_runtime(rt::handle())
                    .set_logger(ServerLogger)
                    .build("127.0.0.1:0"),
            )
                .expect("can build server");
            let server_addr = server.local_addr().expect("has local address");
            let url = format!("http://{}", server_addr);
            let server_handle = server
                .start(AnkrRpcApiServerImpl.into_rpc())
                .expect("can start server");
            let client =
                HttpClientBuilder::default()
                    .build(url)
                    .map_err(|err| Error::Fatal {
                        error: err.to_string(),
                    })?;
            Ok(Self {
                client,
                _sever_handle: server_handle,
            })
        }
    }

    impl<'a> AnkrRpcI<'a> for AnkrRpc {
        fn client(&'a self) -> &'a HttpClient {
            &self.client
        }
    }

    struct AnkrRpcApiServerImpl;

    // Test mock of the Ankr API.
    #[async_trait]
    impl AnkrRpcApiServer for AnkrRpcApiServerImpl {
        async fn get_account_balance(
            &self,
            blockchain: Vec<AnkrBlockchain>,
            pageSize: usize,
            pageToken: Option<&str>,
            walletAddress: &str,
        ) -> RpcResult<AnkrTokenBalances> {
            // Simulate paging once
            let page_token = if pageToken.is_none() {
                Some("page-token".to_string())
            } else {
                None
            };

            let balances = if pageToken.is_none() {
                json!([
              {
                "blockchain": "polygon",
                "tokenName": "USD Coin (PoS)",
                "tokenSymbol": "USDC",
                "tokenDecimals": 6,
                "tokenType": "ERC20",
                "contractAddress": "0x2791bca1f2de4661ed88a30c99a7a9449aa84174",
                "holderAddress": "0x12d7dacca565ee7581f6bbf1eb8f5ccbb456ef19",
                "balance": "0.119157",
                "balanceRawInteger": "119157",
                "balanceUsd": "0.119157",
                "tokenPrice": "1",
                "thumbnail": "https://raw.githubusercontent.com/trustwallet/assets/master/blockchains/polygon/assets/0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174/logo.png"
              },
              {
                "blockchain": "polygon",
                "tokenName": "Polygon",
                "tokenSymbol": "MATIC",
                "tokenDecimals": 18,
                "tokenType": "NATIVE",
                "holderAddress": "0x12d7dacca565ee7581f6bbf1eb8f5ccbb456ef19",
                "balance": "0.941696667609996629",
                "balanceRawInteger": "941696667609996629",
                "balanceUsd": "0",
                "tokenPrice": "0",
                "thumbnail": "https://raw.githubusercontent.com/trustwallet/assets/master/blockchains/ethereum/info/logo.png"
              },
            ])
            } else {
                json!([{
                "blockchain": "polygon",
                "tokenName": "Space Protocol",
                "tokenSymbol": "SPL",
                "tokenDecimals": 18,
                "tokenType": "ERC20",
                "contractAddress": "0xfec6832ab7bea7d3db02472b64cb59cfc6f2c107",
                "holderAddress": "0x12d7dacca565ee7581f6bbf1eb8f5ccbb456ef19",
                "balance": "500",
                "balanceRawInteger": "500000000000000000000",
                "balanceUsd": "0",
                "tokenPrice": "0",
                "thumbnail": ""
            }])
            };

            let balances: Vec<AnkrTokenBalance> =
                serde_json::from_value(balances).expect("correct type mapping");

            Ok(AnkrTokenBalances {
                total_balance_usd: "1".into(),
                assets: balances,
                next_page_token: page_token,
            })
        }
    }

    #[derive(Clone)]
    struct ServerLogger;

    impl HttpLogger for ServerLogger {
        type Instant = Instant;

        fn on_request(
            &self,
            remote_addr: SocketAddr,
            request: &Request<Body>,
        ) -> Self::Instant {
            println!(
                "[Logger::on_request] remote_addr {}, request: {:?}",
                remote_addr, request
            );
            Instant::now()
        }

        fn on_call(&self, name: &str, params: Params, kind: MethodKind) {
            println!(
                "[Logger::on_call] method: '{}', params: {:?}, kind: {}",
                name, params, kind
            );
        }

        fn on_result(&self, name: &str, succeess: bool, started_at: Self::Instant) {
            println!(
                "[Logger::on_result] '{}', worked? {}, time elapsed {:?}",
                name,
                succeess,
                started_at.elapsed()
            );
        }

        fn on_response(&self, result: &str, started_at: Self::Instant) {
            println!(
                "[Logger::on_response] result: {}, time elapsed {:?}",
                result,
                started_at.elapsed()
            );
        }
    }

    #[test]
    fn fungible_token_balances() {
        let ankr = AnkrRpc::new().unwrap();
        let balances = rt::block_on(ankr.get_account_balances(
            ChainId::PolygonMainnet,
            "0x12d7dacca565ee7581f6bbf1eb8f5ccbb456ef19",
        ))
        .unwrap();
        assert_eq!(balances.len(), 2);
    }
}
