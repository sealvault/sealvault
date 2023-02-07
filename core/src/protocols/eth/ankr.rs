// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use ethers::types::{Address, U256};
#[cfg(not(test))]
use jsonrpsee::core::client::CertificateStore;
// Behind flag otherwise `cargo fix` removes it
#[cfg(not(test))]
use jsonrpsee::http_client::HttpClientBuilder;
use jsonrpsee::{
    core::{async_trait, RpcResult},
    http_client::HttpClient,
    proc_macros::rpc,
    types::error::ErrorCode,
};
use serde::{Deserialize, Serialize};
use url::Url;

use crate::{
    protocols::{
        eth::{token::FungibleTokenBalance, ChainId},
        TokenType,
    },
    Error,
};

// Port number is important for, otherwise Jsonrpsee HTTP client doesn't work
#[cfg(not(test))]
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
        pageSize: usize,
        pageToken: Option<&str>,
        walletAddress: &str,
    ) -> RpcResult<AnkrFungibleTokenBalances>;

    #[method(name = "getNFTsByOwner", param_kind = map)]
    async fn get_nfts_by_owner(
        &self,
        walletAddress: &str,
        blockchain: Vec<AnkrBlockchain>,
        pageSize: usize,
        pageToken: Option<&str>,
    ) -> RpcResult<AnkrNFTBalances>;
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
        let mut token_balances: Vec<AnkrFungibleTokenBalance> = Default::default();

        let ankr_chain_id: AnkrBlockchain = chain_id.try_into()?;
        let blockchains: Vec<AnkrBlockchain> = vec![ankr_chain_id];

        loop {
            let result: AnkrFungibleTokenBalances = self
                .client()
                .get_account_balance(
                    blockchains.clone(),
                    PAGE_SIZE,
                    page_token.as_deref(),
                    address,
                )
                .await?;

            let AnkrFungibleTokenBalances {
                next_page_token,
                assets,
                ..
            } = result;
            token_balances.extend(assets);

            page_token = self.normalize_next_page_token(next_page_token);
            if page_token.is_none() {
                break;
            }
        }
        Ok(to_fungible_token_balances(token_balances))
    }

    async fn get_nfts_by_owner(
        &'a self,
        chain_id: ChainId,
        address: &str,
    ) -> Result<Vec<NFTBalance>, Error> {
        let mut page_token: Option<String> = None;
        let mut token_balances: Vec<AnkrNFTBalance> = Default::default();

        let ankr_chain_id: AnkrBlockchain = chain_id.try_into()?;
        let blockchains: Vec<AnkrBlockchain> = vec![ankr_chain_id];

        loop {
            let result: AnkrNFTBalances = self
                .client()
                .get_nfts_by_owner(
                    address,
                    blockchains.clone(),
                    PAGE_SIZE,
                    page_token.as_deref(),
                )
                .await?;

            let AnkrNFTBalances {
                next_page_token,
                assets,
                ..
            } = result;
            token_balances.extend(assets);

            page_token = self.normalize_next_page_token(next_page_token);
            if page_token.is_none() {
                break;
            }
        }
        Ok(to_nft_balances(token_balances))
    }

    fn normalize_next_page_token(&self, token: Option<String>) -> Option<String> {
        token.and_then(|t| if t.is_empty() { None } else { Some(t) })
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
            .certificate_store(CertificateStore::WebPki)
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
    ankr_balances: Vec<AnkrFungibleTokenBalance>,
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

impl TryFrom<AnkrFungibleTokenBalance> for FungibleTokenBalance {
    type Error = Error;

    fn try_from(value: AnkrFungibleTokenBalance) -> Result<Self, Error> {
        if value.token_type != AnkrTokenType::Erc20 {
            return Err(Error::Retriable {
                error: format!(
                    "Invalid token type for fungible token: {}",
                    value.token_type
                ),
            });
        }
        let AnkrFungibleTokenBalance {
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

fn to_nft_balances(ankr_balances: Vec<AnkrNFTBalance>) -> Vec<NFTBalance> {
    ankr_balances
        .into_iter()
        .map(|ankr_token| {
            let nft: NFTBalance = ankr_token.into();
            nft
        })
        .collect()
}

impl From<AnkrNFTBalance> for NFTBalance {
    fn from(value: AnkrNFTBalance) -> Self {
        let AnkrNFTBalance {
            blockchain,
            collection_name,
            name,
            symbol,
            contract_address,
            image_url,
            ..
        } = value;
        let chain_id: ChainId = blockchain.into();
        NFTBalance {
            chain_id,
            contract_address,
            symbol,
            collection_name,
            name,
            image_url,
        }
    }
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

impl TryFrom<ChainId> for AnkrBlockchain {
    type Error = Error;

    fn try_from(chain_id: ChainId) -> Result<Self, Self::Error> {
        match chain_id {
            ChainId::EthMainnet => Ok(AnkrBlockchain::Eth),
            ChainId::PolygonMainnet => Ok(AnkrBlockchain::Polygon),
            _ => Err(Error::JsonRpc {
                code: ErrorCode::InvalidParams,
                message: format!("Chain {chain_id} is not supported for Ankr API"),
            }),
        }
    }
}

impl From<AnkrBlockchain> for ChainId {
    fn from(value: AnkrBlockchain) -> Self {
        match value {
            AnkrBlockchain::Eth => ChainId::EthMainnet,
            AnkrBlockchain::Polygon => ChainId::PolygonMainnet,
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnkrFungibleTokenBalances {
    total_balance_usd: String,
    assets: Vec<AnkrFungibleTokenBalance>,
    next_page_token: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnkrFungibleTokenBalance {
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

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnkrNFTBalances {
    /// Owner address
    owner: Address,
    assets: Vec<AnkrNFTBalance>,
    next_page_token: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnkrNFTBalance {
    blockchain: AnkrBlockchain,
    collection_name: String,
    name: String,
    symbol: String,
    contract_address: Address,
    contract_type: String,
    token_id: String,
    image_url: Option<Url>,
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

use crate::protocols::eth::NFTBalance;

#[cfg(test)]
mod tests {
    use std::{net::SocketAddr, time::Instant};

    use anyhow::anyhow;
    use jsonrpsee::{
        core::{async_trait, RpcResult},
        http_client::{HttpClient, HttpClientBuilder},
        server::{
            logger::{HttpRequest, Logger, MethodKind, TransportProtocol},
            ServerBuilder, ServerHandle,
        },
        types::Params,
    };
    use serde_json::json;

    use super::*;
    use crate::async_runtime as rt;

    pub struct AnkrRpc {
        client: HttpClient,
        _sever_handle: ServerHandle,
    }

    impl AnkrRpc {
        pub fn new() -> Result<Self, Error> {
            let server = rt::block_on(
                ServerBuilder::default()
                    .custom_tokio_runtime(rt::handle())
                    .set_logger(ServerLogger)
                    .build("127.0.0.1:0"),
            )
            .expect("can build server");
            let server_addr = server.local_addr().expect("has local address");
            let url = format!("http://{server_addr}");
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
            _blockchain: Vec<AnkrBlockchain>,
            _pageSize: usize,
            pageToken: Option<&str>,
            _walletAddress: &str,
        ) -> RpcResult<AnkrFungibleTokenBalances> {
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

            let balances: Vec<AnkrFungibleTokenBalance> =
                serde_json::from_value(balances).expect("correct type mapping");

            Ok(AnkrFungibleTokenBalances {
                total_balance_usd: "1".into(),
                assets: balances,
                next_page_token: page_token,
            })
        }

        async fn get_nfts_by_owner(
            &self,
            walletAddress: &str,
            _blockchain: Vec<AnkrBlockchain>,
            _pageSize: usize,
            pageToken: Option<&str>,
        ) -> RpcResult<AnkrNFTBalances> {
            // Simulate paging once
            let next_page_token = if pageToken.is_none() {
                Some("page-token".to_string())
            } else {
                Some("".to_string())
            };

            let balances = if pageToken.is_none() {
                json!([
                    {
                        "blockchain": "polygon",
                        "name": "SealVault Punk Logo 25/100",
                        "tokenId": "25",
                        "tokenUrl": "data:application/json;base64,eyJuYW1lIjogIlNlYWxWYXVsdCBQdW5rIExvZ28gMjUvMTAwIiwgImRlc2NyaXB0aW9uIjogIlRoaXMgTkZUIGNvbW1lbW9yYXRlcyBTZWFsVmF1bHQncyBicmllZiBPRyBwdW5rIHBoYXNlLiBcblxuSW5zcGlyZWQgYnkgQW5keSBXYXJob2wgYW5kIEjDvHNrZXIgRMO8J3MgTmV3IERheSBSaXNpbmcuIiwgImltYWdlIjogImlwZnM6Ly9RbVg1WGJlV2g0cVEzZmlzNjVlV0RBcUdxd3h5R0FqTUNnQlRNOW54Qm50YkRVP2lkPTI1IiwgInByb3BlcnRpZXMiOiB7Im51bWJlciI6IDI1LCAibmFtZSI6ICJTZWFsVmF1bHQgUHVuayBMb2dvIn19",
                        "imageUrl": "https://ipfs.io/ipfs/QmX5XbeWh4qQ3fis65eWDAqGqwxyGAjMCgBTM9nxBntbDU?id=25",
                        "collectionName": "SealVault Punk Logo",
                        "symbol": "SHOWTIME",
                        "contractType": "ERC721",
                        "contractAddress": "0x00e5c88011233605ff5e307a0a2b0d3fc9f9f753"
                    },
                    {
                        "blockchain": "polygon",
                        "name": "fortune 2/100",
                        "tokenId": "2",
                        "tokenUrl": "data:application/json;base64,eyJuYW1lIjogImZvcnR1bmUgMi8xMDAiLCAiZGVzY3JpcHRpb24iOiAiY29va2llIiwgImltYWdlIjogImlwZnM6Ly9RbVZaQ0tueGVrbVBwcVlqYzI4ZmJkNlQxTDQybll1VFRBbzRiaE4xZGhrTnBpP2lkPTIiLCAicHJvcGVydGllcyI6IHsibnVtYmVyIjogMiwgIm5hbWUiOiAiZm9ydHVuZSJ9fQ==",
                        "imageUrl": "https://ipfs.io/ipfs/QmVZCKnxekmPpqYjc28fbd6T1L42nYuTTAo4bhN1dhkNpi?id=2",
                        "collectionName": "fortune",
                        "symbol": "SHOWTIME",
                        "contractType": "ERC721",
                        "contractAddress": "0xcfeed690bcdbbe4772a15868ad78f75fff64634f"
                    },
                ])
            } else {
                json!([{
                    "blockchain": "polygon",
                    "name": "Michael mollusk 291/1000",
                    "tokenId": "291",
                    "tokenUrl": "data:application/json;base64,eyJuYW1lIjogIk1pY2hhZWwgbW9sbHVzayAyOTEvMTAwMCIsICJkZXNjcmlwdGlvbiI6ICJNaWRqb3VybmV5IiwgImltYWdlIjogImlwZnM6Ly9RbVR1bkxNSFhBMW1DMXJKTGhuRW5aWVVHQ1hhYmlha0ZpTkN4N3dOUEpmN0pjP2lkPTI5MSIsICJwcm9wZXJ0aWVzIjogeyJudW1iZXIiOiAyOTEsICJuYW1lIjogIk1pY2hhZWwgbW9sbHVzayJ9fQ==",
                    "imageUrl": "https://ipfs.io/ipfs/QmTunLMHXA1mC1rJLhnEnZYUGCXabiakFiNCx7wNPJf7Jc?id=291",
                    "collectionName": "Michael mollusk",
                    "symbol": "SHOWTIME",
                    "contractType": "ERC721",
                    "contractAddress": "0x14690bb52c6da470f906b6be0db1b6c82d202874"
                }])
            };

            let assets: Vec<AnkrNFTBalance> =
                serde_json::from_value(balances).expect("correct type mapping");

            let owner: Address = walletAddress.parse().map_err(|_| {
                use jsonrpsee::types::error::CallError;
                CallError::InvalidParams(anyhow!("Invalid address: '{walletAddress}'"))
            })?;
            Ok(AnkrNFTBalances {
                owner,
                assets,
                next_page_token,
            })
        }
    }

    #[derive(Clone)]
    struct ServerLogger;

    impl Logger for ServerLogger {
        type Instant = Instant;

        fn on_connect(
            &self,
            remote_addr: SocketAddr,
            req: &HttpRequest,
            _t: TransportProtocol,
        ) {
            println!("[Logger::on_connect] remote_addr {remote_addr:?}, req: {req:?}");
        }

        fn on_request(&self, _t: TransportProtocol) -> Self::Instant {
            Instant::now()
        }

        fn on_call(
            &self,
            name: &str,
            params: Params,
            kind: MethodKind,
            _t: TransportProtocol,
        ) {
            println!(
                "[Logger::on_call] method: '{name}', params: {params:?}, kind: {kind}"
            );
        }

        fn on_result(
            &self,
            name: &str,
            success: bool,
            started_at: Self::Instant,
            _t: TransportProtocol,
        ) {
            println!(
                "[Logger::on_result] '{name}', worked? {success}, time elapsed {:?}",
                started_at.elapsed()
            );
        }

        fn on_response(
            &self,
            result: &str,
            started_at: Self::Instant,
            _t: TransportProtocol,
        ) {
            println!(
                "[Logger::on_response] result: {result}, time elapsed {:?}",
                started_at.elapsed()
            );
        }

        fn on_disconnect(&self, remote_addr: SocketAddr, _t: TransportProtocol) {
            println!("[Logger::on_disconnect] remote_addr: {remote_addr:?}");
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

    #[test]
    fn nft_token_balances() {
        let ankr = AnkrRpc::new().unwrap();
        let balances = rt::block_on(ankr.get_nfts_by_owner(
            ChainId::PolygonMainnet,
            "0x12d7dacca565ee7581f6bbf1eb8f5ccbb456ef19",
        ))
        .unwrap();
        assert_eq!(balances.len(), 3);
    }
}
