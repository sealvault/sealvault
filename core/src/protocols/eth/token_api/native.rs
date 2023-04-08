// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A token API that only uses standard Ethereum JSON-RPC methods to fetch token balances for
//! maximum compatibility. Doesn't support NFTs yet. Doesn't support discovery.

use std::{collections::HashMap, fmt::Debug, num::NonZeroUsize, sync::Arc};

use ethers::{
    abi::AbiDecode,
    contract::FunctionCall,
    providers::{Http, Provider},
    types::{transaction::eip2718::TypedTransaction, Address, U256},
};
use futures::StreamExt;
use itertools::Itertools;
use jsonrpsee::{
    core::{
        client::{CertificateStore, ClientT},
        params::{ArrayParams, BatchRequestBuilder},
        Error as JsonRpcError,
    },
    http_client::HttpClientBuilder,
    rpc_params,
};
use lazy_static::lazy_static;
use strum::IntoEnumIterator;
use strum_macros::{EnumIter, EnumString};
use url::Url;

use crate::{
    config,
    protocols::eth::{
        contracts::ERC20Contract, ChainId, ChecksumAddress, FungibleTokenBalance,
        NativeTokenAmount, RpcManagerI, TokenBalances,
    },
    Error,
};

lazy_static! {
    static ref MAX_BATCH_SIZE: NonZeroUsize = NonZeroUsize::new(1000).expect("static ok");
}

pub struct NativeTokenAPi<'a> {
    max_batch_size: NonZeroUsize,
    rpc_manager: &'a dyn RpcManagerI,
}

#[allow(dead_code)]
impl<'a> NativeTokenAPi<'a> {
    #[allow(dead_code)]
    pub fn new(rpc_manager: &'a dyn RpcManagerI) -> Self {
        Self::new_with_overrides(rpc_manager, *MAX_BATCH_SIZE)
    }

    fn new_with_overrides(
        rpc_manager: &'a dyn RpcManagerI,
        max_batch_size: NonZeroUsize,
    ) -> Self {
        Self {
            rpc_manager,
            max_batch_size,
        }
    }

    /// Fetch token balances through standard Ethereum RPC calls.
    /// Only supports native and ERC20 tokens currently.
    /// `native_tokens` are the chain ids where the address can have native tokens.
    /// `fungible_tokens` is a map from chain ID to ERC20 contract address.
    pub(super) async fn fetch_token_balances(
        &'a self,
        owner_address: ChecksumAddress,
        native_token_chains: Vec<ChainId>,
        fungible_tokens: HashMap<ChainId, Vec<ChecksumAddress>>,
    ) -> Result<Vec<TokenBalances>, Error> {
        let native_tokens = self
            .fetch_native_tokens(owner_address, native_token_chains)
            .await?;

        let mut fungible_tokens = self
            .fetch_fungible_tokens(owner_address, fungible_tokens)
            .await;

        native_tokens
            .into_iter()
            .map(|native_token| {
                let chain_id = native_token.chain_id;
                let fungible_tokens =
                    fungible_tokens.remove(&chain_id).unwrap_or_default();
                Ok(TokenBalances {
                    chain_id,
                    native_token,
                    fungible_tokens,
                    nfts: Default::default(),
                })
            })
            .collect()
    }

    async fn fetch_native_tokens(
        &'a self,
        owner_address: ChecksumAddress,
        chain_ids: impl IntoIterator<Item = ChainId>,
    ) -> Result<Vec<NativeTokenAmount>, Error> {
        let results: Vec<Result<NativeTokenAmount, Error>> =
            futures::stream::iter(chain_ids)
                .map(|chain_id| async move {
                    let provider = self.rpc_manager.eth_api_provider(chain_id);
                    let balance =
                        provider.native_token_balance_async(owner_address).await?;
                    Ok(balance)
                })
                .buffered(config::MAX_ASYNC_CONCURRENT_REQUESTS)
                .collect()
                .await;
        results.into_iter().collect()
    }

    async fn fetch_fungible_tokens(
        &'a self,
        owner_address: ChecksumAddress,
        fungible_tokens: HashMap<ChainId, Vec<ChecksumAddress>>,
    ) -> HashMap<ChainId, Vec<FungibleTokenBalance>> {
        futures::stream::iter(fungible_tokens.into_iter())
            .filter_map(|(chain_id, contract_addresses)| async move {
                let result = self.fetch_fungible_tokens_on_chain(
                    owner_address,
                    chain_id,
                    contract_addresses,
                )
                    .await;
                match result {
                    // `buffered` needs futures but filter map returns values.
                    Ok(result) => Some(async move { (chain_id, result) }),
                    Err(err) => {
                        log::error!("Error fetching fungible token balances for chain id {chain_id}: {err}");
                        None
                    },
                }
            })
            .buffered(config::MAX_ASYNC_CONCURRENT_REQUESTS)
            .collect()
            .await
    }

    async fn fetch_fungible_tokens_on_chain(
        &'a self,
        owner_address: ChecksumAddress,
        chain_id: ChainId,
        fungible_token_addresses: Vec<ChecksumAddress>,
    ) -> Result<Vec<FungibleTokenBalance>, Error> {
        // TODO we don't actually use this so ideally we wouldn't have to create it, but the
        // `ERC20Contract` needs it as argument. We als don't really need the `ERC20Contract`, only the
        // call data, so this could be made a lot more efficient.
        let rpc_endpoint = self.rpc_manager.eth_rpc_endpoint(chain_id);
        let provider = Arc::new(Provider::new(Http::new(rpc_endpoint.clone())));

        let mut calls: Vec<EthCall> = Vec::with_capacity(
            fungible_token_addresses.len() * FunctionName::iter().len(),
        );
        for contract_address in fungible_token_addresses {
            let contract_address: Address = contract_address.into();
            let contract = ERC20Contract::new(contract_address, provider.clone());
            let contract_calls = calls_for_contract(contract, owner_address)?;
            calls.extend(contract_calls);
        }

        let results = self.batch_eth_call(chain_id, calls).await?;

        Ok(call_results_to_balances(chain_id, results))
    }

    async fn batch_eth_call(
        &self,
        chain_id: ChainId,
        calls: Vec<EthCall>,
    ) -> Result<Vec<EthCallResult>, JsonRpcError> {
        let client = HttpClientBuilder::default()
            .certificate_store(CertificateStore::WebPki)
            .build(self.rpc_manager.eth_rpc_endpoint(chain_id))?;

        let mut results: Vec<EthCallResult> = Vec::with_capacity(calls.len());

        for chunk in calls
            .into_iter()
            .chunks(self.max_batch_size.into())
            .into_iter()
        {
            let chunk: Vec<EthCall> = chunk.collect();
            let mut batch = BatchRequestBuilder::new();
            chunk
                .iter()
                .try_for_each(|call| batch.insert(call.method, call.rpc_params()))?;
            let responses = client.batch_request::<'_, '_, '_, String>(batch).await?;
            responses.into_iter().zip(chunk).for_each(|(response, call)| {
                match response {
                    Ok(result) => {
                        results.push(EthCallResult {
                            call,
                            result,
                        })
                    },
                    Err(err) => {
                        log::error!("Error fetching fungible token balance for chain {chain_id}: '{} {}'", err.code(), err.message());
                    },
                }
            });
        }

        Ok(results)
    }
}

#[derive(Clone, Debug, EnumString, EnumIter, strum_macros::Display)]
#[strum(serialize_all = "camelCase")]
pub enum FunctionName {
    BalanceOf,
    Decimals,
    Symbol,
}

#[derive(Debug)]
struct EthCall {
    method: &'static str,
    function: FunctionName,
    address: ChecksumAddress,
    tx: TypedTransaction,
}

impl EthCall {
    fn new(function_name: &str, tx: TypedTransaction) -> Result<Self, Error> {
        let function: FunctionName = function_name.parse().map_err(|_| Error::Fatal {
            // Logic error
            error: "Invalid function name".into(),
        })?;
        let address: ChecksumAddress = tx
            .to_addr()
            .copied()
            .ok_or(Error::Fatal {
                // Logic error
                error: "Transaction doesn't have to address".into(),
            })?
            .into();
        Ok(EthCall {
            method: "eth_call",
            function,
            address,
            tx,
        })
    }

    fn rpc_params(&self) -> ArrayParams {
        rpc_params![&self.tx, "latest"]
    }
}

#[derive(Debug)]
struct EthCallResult {
    call: EthCall,
    result: String,
}

fn calls_for_contract(
    contract: ERC20Contract<Provider<Http>>,
    owner_address: ChecksumAddress,
) -> Result<[EthCall; 3], Error> {
    Ok([
        call_to_request(contract.balance_of(owner_address.into()))?,
        call_to_request(contract.symbol())?,
        call_to_request(contract.decimals())?,
    ])
}

fn call_to_request<B, M, D>(call: FunctionCall<B, M, D>) -> Result<EthCall, Error> {
    EthCall::new(&call.function.name, call.tx)
}

/// Convert `eth_call` results to `FungibleTokenBalance` objects.
fn call_results_to_balances(
    chain_id: ChainId,
    results: Vec<EthCallResult>,
) -> Vec<FungibleTokenBalance> {
    let by_contract =
        results
            .into_iter()
            .fold(HashMap::new(), |mut by_contract, call_result| {
                by_contract
                    .entry(call_result.call.address)
                    .or_insert_with(Vec::new)
                    .push(call_result);
                by_contract
            });

    by_contract
        .into_iter()
        .filter_map(|(contract_address, call_result)| {
            call_result_to_balance(chain_id, contract_address, call_result)
        })
        .collect()
}

fn call_result_to_balance(
    chain_id: ChainId,
    contract_address: ChecksumAddress,
    call_result: Vec<EthCallResult>,
) -> Option<FungibleTokenBalance> {
    let mut balance = None;
    let mut decimals = None;
    let mut symbol = None;
    for result in call_result {
        match result.call.function {
            FunctionName::BalanceOf => balance = Some(result.result),
            FunctionName::Decimals => decimals = Some(result.result),
            FunctionName::Symbol => symbol = Some(result.result),
        }
    }
    let balance = balance?;
    let decimals = decimals?;
    let symbol = symbol?;

    let decimals = u8::decode_hex(decimals).map_or_else(
        |err| {
            log::error!("Failed to parse decimals: {}", err);
            None
        },
        Some,
    )?;
    let balance = U256::decode_hex(balance).map_or_else(
        |err| {
            log::error!("Failed to parse balance: {}", err);
            None
        },
        Some,
    )?;
    let symbol = String::decode_hex(symbol).map_or_else(
        |err| {
            log::error!("Failed to parse symbol: {}", err);
            None
        },
        Some,
    )?;

    Some(FungibleTokenBalance {
        chain_id,
        contract_address,
        amount: balance,
        decimals,
        symbol,
        logo: logo_url(chain_id, &contract_address),
    })
}

/// Fetch the logo url for a given token from Trust Wallet Assets.
/// Not guaranteed that the logo at the url exists. Have to query it to make sure.
fn logo_url(chain_id: ChainId, contract_address: &ChecksumAddress) -> Option<Url> {
    chain_id_to_logo_name(chain_id).and_then(|chain_name| {
        let url = format!(
            "https://raw.githubusercontent.com/trustwallet/assets/master/blockchains/{}/assets/{}/logo.png",
            chain_name,
            contract_address
        );
        Url::parse(&url).map_or_else(
            |err| {
                log::error!("Failed to parse logo url: {}", err);
                None
            },
            Some,
        )
    })
}

fn chain_id_to_logo_name(chain_id: ChainId) -> Option<&'static str> {
    match chain_id {
        ChainId::EthMainnet => Some("ethereum"),
        ChainId::EthGoerli => None,
        ChainId::PolygonMainnet => Some("polygon"),
        ChainId::PolygonMumbai => None,
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;
    use crate::{
        async_runtime as rt, protocols::eth::contracts::test_util::TestContractDeployer,
    };

    #[test]
    fn test_logo_url_ethereum() {
        let expected: Url = "https://raw.githubusercontent.com/trustwallet/assets/master/blockchains/ethereum/assets/0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48/logo.png".parse().unwrap();
        let actual = logo_url(
            ChainId::EthMainnet,
            &"0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48"
                .parse()
                .unwrap(),
        )
        .unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_logo_url_polygon() {
        let expected: Url = "https://raw.githubusercontent.com/trustwallet/assets/master/blockchains/polygon/assets/0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174/logo.png".parse().unwrap();
        let actual = logo_url(
            ChainId::PolygonMainnet,
            &"0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174"
                .parse()
                .unwrap(),
        )
        .unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_token_balances() -> Result<()> {
        // One token needs 3 calls, so batch size of 2 lets us simulate paging.
        let max_batch_size = NonZeroUsize::new(2).unwrap();
        let chain_id = ChainId::EthMainnet;

        let contract_deployer = TestContractDeployer::init(chain_id);
        let contract_address = contract_deployer.deploy_fungible_token_test_contract()?;
        let _rpc_provider = contract_deployer.anvil_rpc.eth_api_provider(chain_id);
        let provider = Arc::new(contract_deployer.provider());
        let contract = ERC20Contract::new(contract_address, provider);
        let symbol = rt::block_on(contract.symbol().call())?;
        assert!(!symbol.is_empty());
        let decimals = rt::block_on(contract.decimals().call())?;
        assert!(decimals > 0);
        let balance = rt::block_on(
            contract
                .balance_of(contract_deployer.deployer_address().into())
                .call(),
        )?;
        assert!(!balance.is_zero());

        let token_api = NativeTokenAPi::new_with_overrides(
            &contract_deployer.anvil_rpc,
            max_batch_size,
        );

        // Two contracts: one that exists and that doesn't to simulate errors.
        let fungible_tokens: HashMap<ChainId, Vec<ChecksumAddress>> =
            vec![(chain_id, vec![Address::random().into(), contract_address])]
                .into_iter()
                .collect();
        let token_balances = rt::block_on(token_api.fetch_token_balances(
            contract_deployer.deployer_address(),
            vec![chain_id],
            fungible_tokens,
        ))?;

        assert_eq!(token_balances.len(), 1);
        let balances = token_balances.into_iter().next().unwrap();

        assert_eq!(balances.chain_id, chain_id);
        assert!(!balances.native_token.amount.is_zero());

        assert_eq!(balances.fungible_tokens.len(), 1);
        assert_eq!(balances.fungible_tokens[0].chain_id, chain_id);
        assert_eq!(
            balances.fungible_tokens[0].contract_address,
            contract_address
        );
        assert_eq!(balances.fungible_tokens[0].symbol, symbol);
        assert_eq!(balances.fungible_tokens[0].decimals, decimals);
        assert_eq!(balances.fungible_tokens[0].amount, balance);
        // There is only a logo, bc we specified Ethereum mainnet as the chain id.
        assert!(balances.fungible_tokens[0].logo.is_some());

        Ok(())
    }
}
