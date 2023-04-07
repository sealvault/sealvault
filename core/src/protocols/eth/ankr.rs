// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::collections::HashMap;

use derive_more::{AsRef, Display, Into};
use ethers::types::{Address, U256};
use jsonrpsee::{
    core::{
        client::{CertificateStore, ClientT},
        params::{BatchRequestBuilder, ObjectParams},
    },
    http_client::{HttpClient, HttpClientBuilder},
};
use serde::{Deserialize, Serialize};
use strum::IntoEnumIterator;
use strum_macros::{EnumIter, EnumString};
use url::Url;

use crate::{
    protocols::{
        eth::{ChainId, NativeTokenAmount},
        FungibleTokenType,
    },
    Error,
};

// Port number is important for, otherwise Jsonrpsee HTTP client doesn't work
const ANKR_API: &str = "https://rpc.ankr.com:443/multichain";
// NFT API doesn't support more than 50
const PAGE_SIZE: usize = 50;

pub struct AnkrApi {
    client: HttpClient,
}

impl AnkrApi {
    pub fn new() -> Result<Self, Error> {
        Self::new_with_overrides(ANKR_API)
    }

    pub fn new_with_overrides(api_endpoint: impl AsRef<str>) -> Result<Self, Error> {
        let client = HttpClientBuilder::default()
            .certificate_store(CertificateStore::WebPki)
            .build(api_endpoint)
            .map_err(|err| Error::Fatal {
                error: err.to_string(),
            })?;
        Ok(Self { client })
    }

    /// Fetch native, fungible and non-fungible token balances for an address on all supported
    /// chains from Ankr Advanced API. If there is no balance on a chain, no `TokenBalances` for
    /// that chain will be returned.
    pub(crate) async fn fetch_token_balances(
        &self,
        owner_address: ChecksumAddress,
    ) -> Result<Vec<TokenBalances>, AnkrRpcError> {
        let mut fungible_page_token: Option<String> = None;
        let mut nft_page_token: Option<String> = None;
        let mut fungible_balances: Vec<AnkrFungibleTokenBalance> = Default::default();
        let mut nft_balances: Vec<AnkrNFTBalance> = Default::default();
        let mut first_call = true;

        loop {
            let mut request = BatchRequestBuilder::new();

            if first_call || fungible_page_token.is_some() {
                let fungible_args = object_params(&owner_address, fungible_page_token)?;
                request.insert("ankr_getAccountBalance", fungible_args)?;
            }
            if first_call || nft_page_token.is_some() {
                let nft_args = object_params(&owner_address, nft_page_token)?;
                request.insert("ankr_getNFTsByOwner", nft_args)?;
            }

            if request.iter().count() == 0 {
                break;
            }

            let results = self.client.batch_request::<AnkrApiResult>(request).await?;
            first_call = false;

            fungible_page_token = None;
            nft_page_token = None;
            for result in results.into_iter() {
                match result {
                    Ok(api_result) => match api_result {
                        AnkrApiResult::GetAccountBalance(balances) => {
                            let AnkrFungibleTokenBalances {
                                next_page_token,
                                assets,
                                ..
                            } = balances;
                            fungible_page_token =
                                normalize_next_page_token(next_page_token);
                            fungible_balances.extend(assets.into_iter());
                        }
                        AnkrApiResult::GetNFTsByOwner(balances) => {
                            let AnkrNFTBalances {
                                next_page_token,
                                assets,
                                ..
                            } = balances;
                            nft_page_token = normalize_next_page_token(next_page_token);
                            nft_balances.extend(assets.into_iter());
                        }
                    },
                    Err(err) => {
                        // Log error and continue
                        log::error!("Ankr API error code: {}", err.code());
                    }
                }
            }
        }

        to_token_balances(fungible_balances, nft_balances)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum AnkrRpcError {
    #[error(transparent)]
    App(#[from] Error),
    #[error(transparent)]
    Serde(#[from] serde_json::Error),
    #[error(transparent)]
    Jsonrpsee(#[from] jsonrpsee::core::Error),
}

impl From<AnkrRpcError> for Error {
    fn from(error: AnkrRpcError) -> Self {
        match error {
            AnkrRpcError::App(source) => source,
            // Retriable in-case it only affects certain requests.
            // May contain private data, so don't log serde error.
            AnkrRpcError::Serde(_) => Error::Retriable {
                error: "Incorrect Ankr API type mappings.".into(),
            },
            AnkrRpcError::Jsonrpsee(source) => source.into(),
        }
    }
}

fn object_params(
    address: &ChecksumAddress,
    next_page_token: Option<String>,
) -> Result<ObjectParams, AnkrRpcError> {
    let mut params = ObjectParams::new();
    params
        .insert::<Vec<AnkrBlockchain>>("blockchain", AnkrBlockchain::iter().collect())?;
    params.insert("walletAddress", address.to_string())?;
    params.insert("pageSize", PAGE_SIZE)?;
    params.insert("pageToken", next_page_token)?;
    Ok(params)
}

fn normalize_next_page_token(token: Option<String>) -> Option<String> {
    token.and_then(|t| if t.is_empty() { None } else { Some(t) })
}

fn to_token_balances(
    fungible_token_balances: Vec<AnkrFungibleTokenBalance>,
    nft_balances: Vec<AnkrNFTBalance>,
) -> Result<Vec<TokenBalances>, AnkrRpcError> {
    let mut balances_by_chain: HashMap<ChainId, TokenBalances> = Default::default();

    for balance in fungible_token_balances.into_iter() {
        match balance.token_type {
            AnkrTokenType::Native => {
                let balance: NativeTokenAmount = balance.try_into()?;
                let balances =
                    balances_by_chain
                        .entry(balance.chain_id)
                        .or_insert_with(|| {
                            TokenBalances::default_for_chain(balance.chain_id)
                        });
                balances.native_token = balance;
            }
            AnkrTokenType::Erc20 => {
                let balance: FungibleTokenBalance = balance.try_into()?;
                let balances =
                    balances_by_chain
                        .entry(balance.chain_id)
                        .or_insert_with(|| {
                            TokenBalances::default_for_chain(balance.chain_id)
                        });
                balances.fungible_tokens.push(balance);
            }
        }
    }

    for balance in nft_balances.into_iter() {
        let balance: NFTBalance = balance.into();
        let balances = balances_by_chain
            .entry(balance.chain_id)
            .or_insert_with(|| TokenBalances::default_for_chain(balance.chain_id));
        balances.nfts.push(balance);
    }

    Ok(balances_by_chain.into_values().collect())
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
            contract_address: contract_address.into(),
            amount: balance_raw_integer.into(),
            decimals: token_decimals,
            symbol: token_symbol,
            logo,
        })
    }
}

impl From<AnkrNFTBalance> for NFTBalance {
    fn from(value: AnkrNFTBalance) -> Self {
        let AnkrNFTBalance {
            blockchain,
            collection_name,
            name,
            symbol,
            contract_address,
            token_id,
            image_url,
            ..
        } = value;
        NFTBalance {
            chain_id: blockchain.into(),
            contract_address: contract_address.into(),
            symbol,
            collection_name,
            name,
            token_id,
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

#[derive(Debug, Serialize, Deserialize)]
#[serde(untagged)]
enum AnkrApiResult {
    GetAccountBalance(AnkrFungibleTokenBalances),
    GetNFTsByOwner(AnkrNFTBalances),
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

use crate::protocols::eth::{
    token_api::{FungibleTokenBalance, NFTBalance, TokenBalances},
    ChecksumAddress,
};

#[cfg(test)]
mod tests {
    use std::{net::SocketAddr, time::Instant};

    use anyhow::{anyhow, Result};
    use jsonrpsee::{
        core::{async_trait, RpcResult},
        proc_macros::rpc,
        server::{
            logger::{HttpRequest, Logger, MethodKind, TransportProtocol},
            ServerBuilder, ServerHandle,
        },
        types::Params,
    };
    use serde_json::json;

    use super::*;
    use crate::async_runtime as rt;

    const TEST_ADDRESS: &str = "0x58853958f16dE02C5b1edfdb49f1c7D8b5308bCE";

    pub struct AnkrRpcTest {
        pub api: AnkrApi,
        _sever_handle: ServerHandle,
    }

    impl AnkrRpcTest {
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
            let api = AnkrApi::new_with_overrides(url)?;
            Ok(Self {
                api,
                _sever_handle: server_handle,
            })
        }
    }

    // Server derive for tests.
    #[rpc(server, namespace = "ankr")]
    trait AnkrRpcApi {
        #[method(name = "getAccountBalance", param_kind = map)]
        async fn get_account_balance(
            &self,
            walletAddress: String,
            blockchain: Vec<AnkrBlockchain>,
            pageSize: usize,
            pageToken: Option<String>,
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

    struct AnkrRpcApiServerImpl;

    // Test mock of the Ankr API.
    #[async_trait]
    impl AnkrRpcApiServer for AnkrRpcApiServerImpl {
        async fn get_account_balance(
            &self,
            walletAddress: String,
            _blockchain: Vec<AnkrBlockchain>,
            _pageSize: usize,
            pageToken: Option<String>,
        ) -> RpcResult<AnkrFungibleTokenBalances> {
            if walletAddress != TEST_ADDRESS {
                return Ok(AnkrFungibleTokenBalances {
                    total_balance_usd: "0".into(),
                    assets: Default::default(),
                    next_page_token: None,
                });
            }
            let balances = if pageToken.is_none() {
                json!([{
                    "blockchain": "polygon_mumbai",
                    "tokenName": "Mumbai Polygon",
                    "tokenSymbol": "MATIC",
                    "tokenDecimals": 18,
                    "tokenType": "NATIVE",
                    "holderAddress": TEST_ADDRESS,
                    "balance": "0.377722525838175",
                    "balanceRawInteger": "377722525838175000",
                    "balanceUsd": "758122.816954017524929879",
                    "tokenPrice": "2007089.239043198448371186",
                    "thumbnail": "https://www.ankr.com/rpc/static/media/polygon.859b6d49.svg"
                },
                {
                    "blockchain": "eth_goerli",
                    "tokenName": "Goerli Ethereum",
                    "tokenSymbol": "GTH",
                    "tokenDecimals": 18,
                    "tokenType": "NATIVE",
                    "holderAddress": TEST_ADDRESS,
                    "balance": "1.34878804811250167",
                    "balanceRawInteger": "1348788048112501670",
                    "balanceUsd": "36879.68160811588817217",
                    "tokenPrice": "27342.829482901656163563",
                    "thumbnail": "https://www.ankr.com/rpc/static/media/eth.3ee8ddd4.svg"
                },
                {
                    "blockchain": "eth",
                    "tokenName": "Matic Token",
                    "tokenSymbol": "MATIC",
                    "tokenDecimals": 18,
                    "tokenType": "ERC20",
                    "contractAddress": "0x7d1afa7b718fb893db30a3abc0cfc608aacfebb0",
                    "holderAddress": TEST_ADDRESS,
                    "balance": "6.2051369",
                    "balanceRawInteger": "6205136900000000000",
                    "balanceUsd": "7.972012197965147476",
                    "tokenPrice": "1.284743967206452363",
                    "thumbnail": "https://raw.githubusercontent.com/trustwallet/assets/master/blockchains/ethereum/assets/0x7D1AfA7B718fb893dB30A3aBc0Cfc608AaCfeBB0/logo.png"
                },])
            } else if pageToken == Some("first-page-token".to_string()) {
                json!([{
                    "blockchain": "polygon",
                    "tokenName": "Polygon",
                    "tokenSymbol": "MATIC",
                    "tokenDecimals": 18,
                    "tokenType": "NATIVE",
                    "holderAddress": TEST_ADDRESS,
                    "balance": "3.101612806260749202",
                    "balanceRawInteger": "3101612806260749202",
                    "balanceUsd": "3.965641407725317588",
                    "tokenPrice": "1.278573972779737886",
                    "thumbnail": "https://www.ankr.com/rpc/static/media/polygon.859b6d49.svg"
                },
                {
                    "blockchain": "polygon",
                    "tokenName": "USD Coin (PoS)",
                    "tokenSymbol": "USDC",
                    "tokenDecimals": 6,
                    "tokenType": "ERC20",
                    "contractAddress": "0x2791bca1f2de4661ed88a30c99a7a9449aa84174",
                    "holderAddress": TEST_ADDRESS,
                    "balance": "2.783265",
                    "balanceRawInteger": "2783265",
                    "balanceUsd": "2.783265",
                    "tokenPrice": "1",
                    "thumbnail": "https://raw.githubusercontent.com/trustwallet/assets/master/blockchains/polygon/assets/0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174/logo.png"
                },])
            } else {
                json!([{
                    "blockchain": "polygon",
                    "tokenName": "(PoS) Dai Stablecoin",
                    "tokenSymbol": "DAI",
                    "tokenDecimals": 18,
                    "tokenType": "ERC20",
                    "contractAddress": "0x8f3cf7ad23cd3cadbd9735aff958023239c6a063",
                    "holderAddress": TEST_ADDRESS,
                    "balance": "0.776958671817900955",
                    "balanceRawInteger": "776958671817900955",
                    "balanceUsd": "0.779110201097638487",
                    "tokenPrice": "1.00276916824250569",
                    "thumbnail": "https://raw.githubusercontent.com/trustwallet/assets/master/blockchains/polygon/assets/0x8f3Cf7ad23Cd3CaDbD9735AFf958023239c6A063/logo.png"
                },])
            };

            let balances: Vec<AnkrFungibleTokenBalance> =
                serde_json::from_value(balances).expect("correct type mapping");

            // Simulate paging
            let page_token = if pageToken.is_none() {
                Some("first-page-token".to_string())
            } else if pageToken == Some("first-page-token".to_string()) {
                Some("second-page-token".to_string())
            } else {
                None
            };

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
            let owner: Address = walletAddress.parse().map_err(|_| {
                use jsonrpsee::types::error::CallError;
                CallError::InvalidParams(anyhow!("Invalid address: '{walletAddress}'"))
            })?;

            if walletAddress != TEST_ADDRESS {
                return Ok(AnkrNFTBalances {
                    owner,
                    assets: Default::default(),
                    next_page_token: Some("".into()),
                });
            }

            let balances = if pageToken.is_none() {
                json!([{
                    "blockchain": "eth_goerli",
                    "name": "Sortcoder NFT 1",
                    "tokenId": "59461660688439608482954753860713749074159004710098681657394853388666171031553",
                    "tokenUrl": "https://testnets-api.opensea.io/api/v1/metadata/0xf4910c763ed4e47a585e2d34baa9a4b611ae448c/59461660688439608482954753860713749074159004710098681657394853388666171031553",
                    "imageUrl": "https://i.seadn.io/gcs/files/eb624f1670216642020b2967b1e04b21.png?w=500&auto=format",
                    "collectionName": "OpenSea Collections",
                    "symbol": "OPENSTORE",
                    "contractType": "ERC1155",
                    "contractAddress": "0xf4910c763ed4e47a585e2d34baa9a4b611ae448c",
                    "quantity": "1"
                },])
            } else {
                json!([{
                    "blockchain": "polygon",
                    "name": "The Lab #271/333",
                    "tokenId": "271",
                    "tokenUrl": "data:application/json;base64,eyJuYW1lIjoiVGhlIExhYiAjMjcxLzMzMyIsImRlc2NyaXB0aW9uIjoiVGhlIExhYiAtIEFJIEFydCBieSB4MSBEZXNpZ25zLlxcblNlZSBtb3JlIGF0IHgxZGVzaWducy5hcnQiLCJleHRlcm5hbF91cmwiOiJodHRwczovL3Nob3d0aW1lLnh5ei9uZnQvcG9seWdvbi8weDA5ZTMwYTUxNEQ4QjJFMGEwMmEwZGYyOEYzZEZjRTQ3MEI1OEZlYjUvMCIsImltYWdlIjoiaXBmczovL1FtV045NWFRZmhtYzVQdFJ2SjltQmlqUlhTaGVmZ00zaWJKUll6alVvYnI0c3IiLCJwcm9wZXJ0aWVzIjp7IkNyZWF0b3IiOiJ4MW92ZXIifX0=",
                    "imageUrl": "https://ipfs.io/ipfs/QmWN95aQfhmc5PtRvJ9mBijRXShefgM3ibJRYzjUobr4sr",
                    "collectionName": "The Lab",
                    "symbol": "✦ SHOWTIME",
                    "contractType": "ERC721",
                    "contractAddress": "0x09e30a514d8b2e0a02a0df28f3dfce470b58feb5"
                },
                {
                    "blockchain": "polygon",
                    "name": "BoredApePizzaClub",
                    "tokenId": "1",
                    "tokenUrl": "https://ipfs.io/ipfs/bafkreieyff2z32vjkcd56z5jppxss6geufkv32tqijfwtqkzpksyspssum",
                    "imageUrl": "https://ipfs.io/ipfs/bafybeialit2d242tryby463rmlasyoatb3qtsaaz22qk73ja2gphi36eri",
                    "collectionName": "Infinity Pizza Promo",
                    "symbol": "PIZZA",
                    "contractType": "ERC1155",
                    "contractAddress": "0x88c830a80d189e24cf2972221e577cd080d7c428",
                    "quantity": "1",
                    "traits": [
                        {
                            "trait_type": "Kategory",
                            "value": "Promo"
                        },
                        {
                            "trait_type": "Twitter",
                            "value": "@BoredPizzas"
                        }
                    ]
                }])
            };

            let assets: Vec<AnkrNFTBalance> =
                serde_json::from_value(balances).expect("correct type mapping");

            // Simulate paging once
            let next_page_token = if pageToken.is_none() {
                Some("page-token".to_string())
            } else {
                Some("".to_string())
            };

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
    fn fetch_token_balances() -> Result<()> {
        let ankr = AnkrRpcTest::new()?;
        let results = rt::block_on(ankr.api.fetch_token_balances(TEST_ADDRESS.parse()?))?;

        assert_eq!(results.len(), 4);

        for balances in results.into_iter() {
            match balances.native_token.chain_id {
                ChainId::EthMainnet => {
                    assert_eq!(balances.native_token.amount, U256::zero());
                    assert_eq!(balances.fungible_tokens.len(), 1);
                }
                ChainId::EthGoerli => {
                    assert_ne!(balances.native_token.amount, U256::zero());
                    assert_eq!(balances.nfts.len(), 1);
                }
                ChainId::PolygonMainnet => {
                    assert_ne!(balances.native_token.amount, U256::zero());
                    assert_eq!(balances.fungible_tokens.len(), 2);
                    assert_eq!(balances.nfts.len(), 2);
                }
                ChainId::PolygonMumbai => {
                    assert_ne!(balances.native_token.amount, U256::zero());
                }
            }
        }
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
