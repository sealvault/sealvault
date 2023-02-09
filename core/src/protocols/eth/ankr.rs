// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashMap, future::Future};

use derive_more::{AsRef, Display, Into};
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
};
use serde::{Deserialize, Serialize};
use strum::IntoEnumIterator;
use strum_macros::{EnumIter, EnumString};
use url::Url;

use crate::{
    protocols::{
        eth::{
            token::FungibleTokenBalance, ChainId, NFTBalance, NativeTokenAmount,
            TokenBalances,
        },
        FungibleTokenType,
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
        pageToken: Option<String>,
        walletAddress: String,
    ) -> RpcResult<AnkrFungibleTokenBalances>;

    #[method(name = "getNFTsByOwner", param_kind = map)]
    async fn get_nfts_by_owner(
        &self,
        walletAddress: String,
        blockchain: Vec<AnkrBlockchain>,
        pageSize: usize,
        pageToken: Option<String>,
    ) -> RpcResult<AnkrNFTBalances>;
}

/// The purpose of this trait is to let us mock the Ankr backend for tests.
/// It's async to make it easy to fetch multiple addresses concurrently.
#[async_trait]
pub trait AnkrRpcI<'a> {
    fn client(&'a self) -> &'a HttpClient;

    async fn paged_call<R, T, F, Fut, G>(
        &'a self,
        address: &str,
        mut callback: F,
        mut extract: G,
    ) -> Result<Vec<T>, Error>
    where
        R: Deserialize<'static> + Send,
        T: Deserialize<'static> + Send,
        F: FnMut(Option<String>, Vec<AnkrBlockchain>, String) -> Fut + Send,
        Fut: Future<Output = RpcResult<R>> + Send,
        G: FnMut(R) -> (Option<String>, Vec<T>) + Send,
    {
        let mut page_token: Option<String> = None;
        let mut results: Vec<T> = Default::default();
        loop {
            // Fetch all supported blockchains
            let blockchains: Vec<AnkrBlockchain> = AnkrBlockchain::iter().collect();
            let result: R =
                callback(page_token, blockchains, address.to_string()).await?;
            let (next_page_token, batch) = extract(result);

            results.extend(batch);

            page_token = self.normalize_next_page_token(next_page_token);
            if page_token.is_none() {
                break;
            }
        }
        Ok(results)
    }

    /// Fetch account balances for an address on all supported chains from an Ankr advanced API.
    async fn get_account_balances(
        &'a self,
        address: &str,
    ) -> Result<Vec<TokenBalances>, Error> {
        let results: Vec<AnkrFungibleTokenBalance> = self
            .paged_call(
                address,
                |page_token: Option<String>,
                 blockchains: Vec<AnkrBlockchain>,
                 address: String| {
                    self.client().get_account_balance(
                        blockchains,
                        PAGE_SIZE,
                        page_token,
                        address,
                    )
                },
                |result: AnkrFungibleTokenBalances| {
                    let AnkrFungibleTokenBalances {
                        next_page_token,
                        assets,
                        ..
                    } = result;
                    (next_page_token, assets)
                },
            )
            .await?;

        to_token_balances(results)
    }

    /// Fetch NFTs for an address on all supported chains from an Ankr advanced API.
    async fn get_nfts_by_owner(
        &'a self,
        address: &str,
    ) -> Result<Vec<NFTBalance>, Error> {
        let results: Vec<AnkrNFTBalance> = self
            .paged_call(
                address,
                |page_token: Option<String>,
                 blockchains: Vec<AnkrBlockchain>,
                 address: String| {
                    self.client().get_nfts_by_owner(
                        address,
                        blockchains,
                        PAGE_SIZE,
                        page_token,
                    )
                },
                |result: AnkrNFTBalances| {
                    let AnkrNFTBalances {
                        next_page_token,
                        assets,
                        ..
                    } = result;
                    (next_page_token, assets)
                },
            )
            .await?;

        Ok(to_nft_balances(results))
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

fn to_token_balances(
    ankr_balances: Vec<AnkrFungibleTokenBalance>,
) -> Result<Vec<TokenBalances>, Error> {
    let mut native_tokens: Vec<NativeTokenAmount> = Default::default();
    let mut fungible_tokens: Vec<FungibleTokenBalance> = Default::default();

    for balance in ankr_balances.into_iter() {
        match balance.token_type {
            AnkrTokenType::Native => {
                let native_token: NativeTokenAmount = balance.try_into()?;
                native_tokens.push(native_token);
            }
            AnkrTokenType::Erc20 => {
                let fungible_token: FungibleTokenBalance = balance.try_into()?;
                fungible_tokens.push(fungible_token);
            }
        }
    }

    let mut fungible_tokens_by_chain: HashMap<ChainId, Vec<FungibleTokenBalance>> =
        Default::default();
    for fungible_token in fungible_tokens.into_iter() {
        let tokens = fungible_tokens_by_chain
            .entry(fungible_token.chain_id)
            .or_default();
        tokens.push(fungible_token);
    }

    let mut results: Vec<TokenBalances> = Vec::with_capacity(native_tokens.len());
    for native_token in native_tokens {
        let fungible_tokens = fungible_tokens_by_chain
            .remove(&native_token.chain_id)
            .unwrap_or_default();
        results.push(TokenBalances {
            native_token,
            fungible_tokens,
        })
    }

    Ok(results)
}

impl TryFrom<AnkrFungibleTokenBalance> for NativeTokenAmount {
    type Error = Error;

    fn try_from(value: AnkrFungibleTokenBalance) -> Result<Self, Self::Error> {
        if value.token_type != AnkrTokenType::Native {
            // Logic error in the app
            return Err(Error::Fatal {
                error: format!(
                    "Invalid token type for Ankr native token: {}",
                    value.token_type
                ),
            });
        }
        let chain_id: ChainId = value.blockchain.into();

        if value.token_decimals != chain_id.native_token().decimals() {
            // Logic error in Ankr API
            return Err(Error::Retriable {
                error: format!(
                    "Invalid decimals for native token from Ankr API: {chain_id}",
                ),
            });
        }

        Ok(NativeTokenAmount::new(
            chain_id,
            value.balance_raw_integer.into(),
        ))
    }
}

impl TryFrom<AnkrFungibleTokenBalance> for FungibleTokenBalance {
    type Error = Error;

    fn try_from(value: AnkrFungibleTokenBalance) -> Result<Self, Error> {
        if value.token_type != AnkrTokenType::Erc20 {
            // Logic error
            return Err(Error::Fatal {
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
                "Missing contract address for ERC20 token '{token_symbol}' on {blockchain} chain"
            ),
        })?;
        let logo = Url::parse(&thumbnail).ok();
        Ok(Self {
            chain_id: blockchain.into(),
            contract_address,
            amount: balance_raw_integer.into(),
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
        NFTBalance {
            chain_id: blockchain.into(),
            contract_address,
            symbol,
            collection_name,
            name,
            image_url,
        }
    }
}

#[derive(
    Clone, Debug, Serialize, Deserialize, EnumString, EnumIter, strum_macros::Display,
)]
#[strum(serialize_all = "snake_case")]
#[serde(rename_all = "snake_case")]
pub enum AnkrBlockchain {
    Eth,
    EthGoerli,
    Polygon,
    PolygonMumbai,
}

impl From<ChainId> for AnkrBlockchain {
    fn from(chain_id: ChainId) -> Self {
        match chain_id {
            ChainId::EthMainnet => AnkrBlockchain::Eth,
            ChainId::EthGoerli => AnkrBlockchain::EthGoerli,
            ChainId::PolygonMainnet => AnkrBlockchain::Polygon,
            ChainId::PolygonMumbai => AnkrBlockchain::PolygonMumbai,
        }
    }
}

impl From<AnkrBlockchain> for ChainId {
    fn from(value: AnkrBlockchain) -> Self {
        match value {
            AnkrBlockchain::Eth => ChainId::EthMainnet,
            AnkrBlockchain::EthGoerli => ChainId::EthGoerli,
            AnkrBlockchain::Polygon => ChainId::PolygonMainnet,
            AnkrBlockchain::PolygonMumbai => ChainId::PolygonMumbai,
        }
    }
}

#[derive(
    Debug,
    Clone,
    Eq,
    PartialEq,
    PartialOrd,
    Ord,
    Hash,
    Into,
    Display,
    AsRef,
    Serialize,
    Deserialize,
)]
#[serde(try_from = "String")]
#[serde(into = "String")]
#[repr(transparent)]
pub struct AnkrBalanceRawInteger(U256);

impl TryFrom<String> for AnkrBalanceRawInteger {
    type Error = Error;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        let amount = U256::from_dec_str(&value).map_err(|_| Error::Retriable {
            error: format!("Invalid raw integer balance from Ankr API: '{value}'"),
        })?;
        Ok(Self(amount))
    }
}

impl From<AnkrBalanceRawInteger> for String {
    fn from(value: AnkrBalanceRawInteger) -> Self {
        value.to_string()
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
    balance_raw_integer: AnkrBalanceRawInteger,
    balance_usd: String,
    token_price: String,
    // Not URL, because it can be empty string.
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
    Debug, Eq, PartialEq, Serialize, Deserialize, EnumString, strum_macros::Display,
)]
#[strum(serialize_all = "UPPERCASE")]
#[serde(rename_all = "UPPERCASE")]
pub enum AnkrTokenType {
    Native,
    Erc20,
}

impl From<AnkrTokenType> for FungibleTokenType {
    fn from(value: AnkrTokenType) -> Self {
        match value {
            AnkrTokenType::Native => FungibleTokenType::Native,
            AnkrTokenType::Erc20 => FungibleTokenType::Custom,
        }
    }
}

#[cfg(test)]
pub use tests::AnkrRpc;

#[cfg(test)]
mod tests {
    use std::{net::SocketAddr, time::Instant};

    use anyhow::{anyhow, Result};
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
            pageToken: Option<String>,
            _walletAddress: String,
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
            walletAddress: String,
            _blockchain: Vec<AnkrBlockchain>,
            _pageSize: usize,
            pageToken: Option<String>,
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
    fn fungible_token_balances() -> Result<()> {
        let ankr = AnkrRpc::new().unwrap();
        let mut balances = rt::block_on(
            ankr.get_account_balances("0x12d7dacca565ee7581f6bbf1eb8f5ccbb456ef19"),
        )?;
        assert_eq!(balances.len(), 1);
        let balance = balances.pop().unwrap();
        assert_eq!(balance.fungible_tokens.len(), 2);
        Ok(())
    }

    #[test]
    fn nft_token_balances() -> Result<()> {
        let ankr = AnkrRpc::new().unwrap();
        let balances = rt::block_on(
            ankr.get_nfts_by_owner("0x12d7dacca565ee7581f6bbf1eb8f5ccbb456ef19"),
        )
        .unwrap();
        assert_eq!(balances.len(), 3);
        Ok(())
    }

    #[test]
    fn ankr_balance_raw_integer() -> Result<()> {
        let s = r#""941696667609996629""#;
        let balance: AnkrBalanceRawInteger = serde_json::from_str(s)?;
        assert_eq!(serde_json::to_string(&balance)?, s);
        Ok(())
    }
}
