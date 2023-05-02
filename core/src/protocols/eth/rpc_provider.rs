// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{fmt::Debug, sync::Arc};

use async_trait::async_trait;
use ethers::{
    core::types::{BlockNumber, Eip1559TransactionRequest, H256},
    middleware::{
        gas_escalator::{Frequency, GasEscalatorMiddleware, GeometricGasPrice},
        gas_oracle::{
            self as gas_oracle, GasCategory, GasOracle, GasOracleError,
            GasOracleMiddleware,
        },
        MiddlewareBuilder, NonceManagerMiddleware,
    },
    providers::{
        Http, Middleware, MiddlewareError, PendingTransaction, Provider, ProviderError,
    },
    types::{Address, BlockId, U256},
    utils::eip1559_default_estimator,
};
use serde::Serialize;
use url::Url;

use crate::{
    async_runtime as rt, config,
    encryption::Keychain,
    protocols::eth::{
        contracts::ERC20Contract,
        signer::{SignerMiddleware, SignerMiddlewareError},
        token::FungibleToken,
        ChainId, ChecksumAddress, EncryptedSigningKey, FungibleTokenAmount,
        NativeTokenAmount,
    },
    Error,
};

type ProviderType = Provider<Http>;

// Ethers `Middleware` is not object safe hence the complex type.
type SignerMiddlewareType = NonceManagerMiddleware<
    GasOracleMiddleware<
        SignerMiddleware<GasEscalatorMiddleware<ProviderType>>,
        Box<dyn GasOracle>,
    >,
>;

/// A trait to let us inject local servers at test time.
#[async_trait]
pub trait RpcManagerI: Debug + Send + Sync {
    fn eth_rpc_endpoint(&self, chain_id: ChainId) -> Url;

    fn ethers_provider(&self, chain_id: ChainId) -> ProviderType;

    fn eth_api_provider(&self, chain_id: ChainId) -> RpcProvider {
        RpcProvider::new(chain_id, self.ethers_provider(chain_id))
    }

    async fn eth_signer_provider_async(
        &self,
        keychain: Arc<Keychain>,
        encrypted_signing_key: EncryptedSigningKey,
    ) -> SignerRpcProvider {
        let chain_id = encrypted_signing_key.chain_id;
        let provider = self.ethers_provider(chain_id);
        let gas_oracle = self.eth_gas_oracle(chain_id);
        SignerRpcProvider::new_async(
            provider,
            gas_oracle,
            keychain,
            encrypted_signing_key,
        )
        .await
    }

    fn eth_signer_provider(
        &self,
        keychain: Arc<Keychain>,
        encrypted_signing_key: EncryptedSigningKey,
    ) -> SignerRpcProvider {
        rt::block_on(self.eth_signer_provider_async(keychain, encrypted_signing_key))
    }

    fn eth_gas_oracle(&self, chain_id: ChainId) -> Box<dyn GasOracle>;

    // This has to be async, because the local jsonrpsee server is built with an async method.
    async fn ankr_api_client(&self) -> Result<jsonrpsee::http_client::HttpClient, Error>;
}

/// Factory for RPC providers.
#[derive(Debug, Default)]
pub struct RpcManager {}

impl RpcManager {
    pub fn new() -> Self {
        Self {}
    }
}

#[async_trait]
impl RpcManagerI for RpcManager {
    fn eth_rpc_endpoint(&self, chain_id: ChainId) -> Url {
        chain_id.http_rpc_endpoint()
    }

    fn ethers_provider(&self, chain_id: ChainId) -> ProviderType {
        let http_endpoint = self.eth_rpc_endpoint(chain_id);
        Provider::new(Http::new(http_endpoint))
    }

    fn eth_gas_oracle(&self, chain_id: ChainId) -> Box<dyn GasOracle> {
        match chain_id {
            ChainId::EthMainnet => Box::new(gas_oracle::GasNow::new()),
            ChainId::EthGoerli => Box::new(gas_oracle::ProviderOracle::new(
                self.ethers_provider(chain_id),
            )),
            ChainId::PolygonMainnet => Box::new(
                gas_oracle::Polygon::new(chain_id.into())
                    .expect("chain is valid")
                    .category(GasCategory::Fast),
            ),
            ChainId::PolygonMumbai => Box::new(
                gas_oracle::Polygon::new(chain_id.into())
                    .expect("chain is valid")
                    .category(GasCategory::Fast),
            ),
            ChainId::FilecoinHyperspaceTestnet => Box::new(
                gas_oracle::ProviderOracle::new(self.ethers_provider(chain_id)),
            ),
            ChainId::ZkSync => Box::new(GasOracleWithoutFeeHistory::new(
                self.ethers_provider(chain_id),
            )),
            ChainId::ZkSyncTestnet => Box::new(GasOracleWithoutFeeHistory::new(
                self.ethers_provider(chain_id),
            )),
        }
    }

    async fn ankr_api_client(&self) -> Result<jsonrpsee::http_client::HttpClient, Error> {
        let client = jsonrpsee::http_client::HttpClientBuilder::default()
            .certificate_store(jsonrpsee::core::client::CertificateStore::WebPki)
            .build(config::ANKR_API)
            .map_err(|err| Error::Fatal {
                error: err.to_string(),
            })?;
        Ok(client)
    }
}

/// A gas oracle that estimates fees without gas price history.
/// This is required for ZkSync that doesn't support `eth_feeHistory`.
#[derive(Clone, Debug)]
#[must_use]
struct GasOracleWithoutFeeHistory<M: Middleware> {
    provider: M,
}

impl<M: Middleware> GasOracleWithoutFeeHistory<M> {
    pub fn new(provider: M) -> Self {
        Self { provider }
    }

    fn map_err(error: ProviderError) -> GasOracleError {
        GasOracleError::ProviderError(Box::new(error))
    }
}

#[cfg_attr(target_arch = "wasm32", async_trait(?Send))]
#[cfg_attr(not(target_arch = "wasm32"), async_trait)]
impl<M: Middleware> GasOracle for GasOracleWithoutFeeHistory<M>
where
    M::Error: 'static,
{
    async fn fetch(&self) -> Result<U256, GasOracleError> {
        self.provider
            .get_gas_price()
            .await
            .map_err(|err| GasOracleError::ProviderError(Box::new(err)))
    }

    async fn estimate_eip1559_fees(&self) -> Result<(U256, U256), GasOracleError> {
        let base_fee_per_gas = self
            .provider
            .get_block(BlockNumber::Latest)
            .await
            .map_err(|err| GasOracleError::ProviderError(Box::new(err)))?
            .ok_or_else(|| ProviderError::CustomError("Latest block not found".into()))
            .map_err(Self::map_err)?
            .base_fee_per_gas
            .ok_or_else(|| ProviderError::CustomError("EIP-1559 not activated".into()))
            .map_err(Self::map_err)?;

        Ok(eip1559_default_estimator(
            base_fee_per_gas,
            Default::default(),
        ))
    }
}

/// Common Ethereum RPC provider methods.
#[async_trait]
pub trait BaseProvider
where
    Self: Sync,
{
    fn provider(&self) -> &ProviderType;
    fn chain_id(&self) -> ChainId;

    /// Proxy an Ethereum RPC request from an in-page request to the API provider.
    fn proxy_rpc_request<T>(
        &self,
        method: &str,
        params: T,
    ) -> Result<serde_json::Value, Error>
    where
        T: Debug + Serialize + Send + Sync,
    {
        rt::block_on(self.proxy_rpc_request_async(method, params))
    }

    async fn proxy_rpc_request_async<T>(
        &self,
        method: &str,
        params: T,
    ) -> Result<serde_json::Value, Error>
    where
        T: Debug + Serialize + Send + Sync,
    {
        // Need to make type concrete and convert error
        let res: serde_json::Value = self.provider().request(method, params).await?;
        Ok(res)
    }

    fn fungible_token_symbol(
        &self,
        contract_address: ChecksumAddress,
    ) -> Result<String, Error> {
        rt::block_on(self.fungible_token_symbol_async(contract_address))
    }

    async fn fungible_token_symbol_async(
        &self,
        contract_address: ChecksumAddress,
    ) -> Result<String, Error> {
        let provider = Arc::new(self.provider().clone());
        let contract = ERC20Contract::new(contract_address, provider);

        let contract_call = contract.symbol();
        let symbol: String =
            contract_call.call().await.map_err(|err| Error::Retriable {
                error: err.to_string(),
            })?;
        Ok(symbol)
    }

    /// Fetch the native token balance for an address.
    fn native_token_balance(
        &self,
        address: ChecksumAddress,
    ) -> Result<NativeTokenAmount, Error> {
        rt::block_on(self.native_token_balance_async(address))
    }

    async fn native_token_balance_async(
        &self,
        address: ChecksumAddress,
    ) -> Result<NativeTokenAmount, Error> {
        let block_id: Option<BlockId> = Some(BlockNumber::Latest.into());
        let balance = self
            .provider()
            .get_balance(address.to_address(), block_id)
            .await?;
        let amount = NativeTokenAmount::new(self.chain_id(), balance);
        Ok(amount)
    }

    fn wait_for_confirmation(&self, tx_hash: H256) -> Result<String, Error> {
        rt::block_on(self.wait_for_confirmation_async(tx_hash))
    }

    async fn wait_for_confirmation_async(&self, tx_hash: H256) -> Result<String, Error> {
        let pending_tx = PendingTransaction::new(tx_hash, self.provider());
        let tx_receipt = pending_tx
            .await
            .map_err(tx_failed_with_error)?
            .ok_or_else(tx_failed_error)?;
        Ok(display_tx_hash(tx_receipt.transaction_hash))
    }
}

/// Ethereum RPC provider with signing capabilities.
#[derive(Clone, Debug)]
pub struct SignerRpcProvider {
    // Needs to be `Arc`, because `Middleware` is not `Clone`, but we need to clone it to pass it to
    // `ERC20Contract`.
    pub(super) provider: Arc<SignerMiddlewareType>,
    pub(super) chain_id: ChainId,
    pub(super) sender_address: Address,
}

impl SignerRpcProvider {
    pub fn new(
        provider: ProviderType,
        gas_oracle: Box<dyn GasOracle>,
        keychain: Arc<Keychain>,
        encrypted_signing_key: EncryptedSigningKey,
    ) -> Self {
        rt::block_on(Self::new_async(
            provider,
            gas_oracle,
            keychain,
            encrypted_signing_key,
        ))
    }

    // This has to be async, because `GasEscalator` does a `spawn` in `new` which requires a runtime.
    pub async fn new_async(
        provider: ProviderType,
        gas_oracle: Box<dyn GasOracle>,
        keychain: Arc<Keychain>,
        encrypted_signing_key: EncryptedSigningKey,
    ) -> Self {
        let chain_id = encrypted_signing_key.chain_id;
        let sender_address: Address = encrypted_signing_key.address.into();

        let max_gas_price = chain_id.max_gas_price();
        let escalator = GeometricGasPrice::new(
            config::GAS_ESCALATOR_COEFFICIENT,
            config::GAS_ESCALATOR_INTERVAL_SEC,
            Some(max_gas_price),
        );

        let provider = provider
            .wrap_into(|p| {
                GasEscalatorMiddleware::new(
                    p,
                    escalator,
                    // Not using per block, because that requires websocket provider to subscribe to
                    // new blocks. +1 to make sure that when the middleware runs, the escalator has
                    // a new value.
                    Frequency::Duration(config::GAS_ESCALATOR_INTERVAL_SEC * 1000 + 1),
                )
            })
            .wrap_into(|p| SignerMiddleware::new(p, keychain, encrypted_signing_key))
            .wrap_into(|p| GasOracleMiddleware::new(p, gas_oracle))
            .wrap_into(|p| NonceManagerMiddleware::new(p, sender_address));

        Self {
            provider: Arc::new(provider),
            chain_id,
            sender_address,
        }
    }

    fn map_err(error: <SignerMiddlewareType as Middleware>::Error) -> Error {
        match error.as_error_response() {
            Some(jsonrpc_error) => jsonrpc_error.into(),
            None => match error.as_provider_error() {
                Some(provider_error) => provider_error.into(),
                None => error
                    .as_inner()
                    .and_then(|inner| inner.as_inner())
                    .and_then(|inner| match inner {
                        SignerMiddlewareError::Middleware(_) => None,
                        SignerMiddlewareError::App(app) => Some(app.clone()),
                    })
                    .unwrap_or_else(|| Error::Retriable {
                        error: error.to_string(),
                    }),
            },
        }
    }

    /// Submit a transaction to the network signed with the signing key.
    /// Returns the transaction hash.
    pub fn send_transaction(&self, tx: Eip1559TransactionRequest) -> Result<H256, Error> {
        rt::block_on(self.send_transaction_async(tx))
    }

    /// Submit a transaction to the network signed with the signing key asynchronously.
    /// Returns the transaction hash.
    pub async fn send_transaction_async(
        &self,
        tx: Eip1559TransactionRequest,
    ) -> Result<H256, Error> {
        let pending_tx = self
            .provider
            // Important that block parameter is `None`, because Filecoin network doesn't support
            // block parameter for `eth_estimateGas`.
            .send_transaction(tx, None)
            .await
            .map_err(Self::map_err)?;
        Ok(pending_tx.tx_hash())
    }

    /// Transfer native token on an Ethereum protocol network.
    /// Returns the transaction hash that can be used to poll for the result.
    pub fn transfer_native_token(
        &self,
        to_checksum_address: ChecksumAddress,
        amount: &NativeTokenAmount,
    ) -> Result<H256, Error> {
        rt::block_on(self.transfer_native_token_async(to_checksum_address, amount))
    }

    pub async fn transfer_native_token_async(
        &self,
        to_address: ChecksumAddress,
        amount: &NativeTokenAmount,
    ) -> Result<H256, Error> {
        if amount.chain_id != self.chain_id {
            return Err(Error::Fatal {
                error: format!(
                    "Rpc provider and amount chain ids must match. Got {} and {}.",
                    self.chain_id, amount.chain_id
                ),
            });
        }

        let tx = Eip1559TransactionRequest::new()
            .to(to_address.to_address())
            .value(amount.amount)
            .from(self.sender_address);

        let tx_hash = self.send_transaction_async(tx).await?;

        Ok(tx_hash)
    }

    /// Transfer native token on an Ethereum protocol network.
    /// Returns the transaction hash that can be used to poll for the result.
    pub fn transfer_fungible_token(
        &self,
        to_address: ChecksumAddress,
        amount_decimal: &str,
        contract_address: ChecksumAddress,
    ) -> Result<H256, Error> {
        let future = self.transfer_fungible_token_async(
            to_address,
            amount_decimal,
            contract_address,
        );
        rt::block_on(future)
    }

    pub async fn transfer_fungible_token_async(
        &self,
        to_address: ChecksumAddress,
        amount_decimal: &str,
        contract_address: ChecksumAddress,
    ) -> Result<H256, Error> {
        let contract = ERC20Contract::new(contract_address, self.provider.clone());

        let contract_call = contract.decimals();
        let decimals: u8 =
            contract_call.call().await.map_err(|err| Error::Retriable {
                error: err.to_string(),
            })?;
        let fungible_token =
            FungibleToken::new(self.chain_id, contract_address, decimals);
        let fungible_token_amount =
            FungibleTokenAmount::new_from_decimal(fungible_token, amount_decimal)?;

        let contract_call =
            contract.transfer(to_address.to_address(), fungible_token_amount.amount);
        let pending_tx = contract_call.send().await.map_err(|err| Error::Retriable {
            error: err.to_string(),
        })?;
        Ok(pending_tx.tx_hash())
    }
}

impl BaseProvider for SignerRpcProvider {
    fn provider(&self) -> &ProviderType {
        self.provider.provider()
    }

    fn chain_id(&self) -> ChainId {
        self.chain_id
    }
}

/// Ethereum RPC provider without signing capabilities.
#[derive(Clone, Debug)]
pub struct RpcProvider {
    pub(super) provider: ProviderType,
    pub(super) chain_id: ChainId,
}

impl RpcProvider {
    pub fn new(chain_id: ChainId, provider: ProviderType) -> Self {
        Self { provider, chain_id }
    }
}

impl BaseProvider for RpcProvider {
    fn provider(&self) -> &ProviderType {
        &self.provider
    }

    fn chain_id(&self) -> ChainId {
        self.chain_id
    }
}

fn display_tx_hash(tx_hash: H256) -> String {
    // Custom formatting is needed, because default display implementation elides.
    // See: https://stackoverflow.com/a/57350190
    format!("{:#x}", tx_hash)
}

const TX_FAILED_MESSAGE: &str = "Transaction failed";

fn tx_failed_with_error(err: ethers::providers::ProviderError) -> Error {
    log::error!("{}: {:?}", TX_FAILED_MESSAGE, err);
    tx_failed_error()
}

fn tx_failed_error() -> Error {
    Error::User {
        explanation: TX_FAILED_MESSAGE.into(),
    }
}

#[cfg(test)]
pub mod local {
    use std::{
        fmt::Formatter,
        sync::{Arc, RwLock},
        time::Duration,
    };

    use ethers::{
        core::utils::{Anvil, AnvilInstance},
        signers::{coins_bip39::English, LocalWallet, MnemonicBuilder},
        types::U256,
    };

    use super::*;
    use crate::protocols::eth::ankr::tests::AnkrRpcTest;

    const MNEMONIC: &str = "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about";
    const POLL_INTERVAL_MS: u64 = 10;

    pub struct LocalRpcManager {
        // Lazy initialized Anvil instance.
        anvil_instance: Arc<RwLock<Option<AnvilInstance>>>,
        /// Lazy initialized Ankr RPC test server.
        ankr_rpc_test: Arc<RwLock<Option<AnkrRpcTest>>>,
    }

    impl LocalRpcManager {
        pub fn new() -> Self {
            let anvil_instance = Arc::new(RwLock::new(None));
            let ankr_rpc_test = Arc::new(RwLock::new(None));
            Self {
                anvil_instance,
                ankr_rpc_test,
            }
        }

        pub(super) fn anvil_endpoint(&self, chain_id: ChainId) -> Url {
            let is_started: bool = {
                let maybe_anvil = self.anvil_instance.read().unwrap();
                maybe_anvil.is_some()
            };
            if !is_started {
                let av = Anvil::new()
                    .chain_id(chain_id as u64)
                    .mnemonic(MNEMONIC)
                    .spawn();
                let _ = self.anvil_instance.write().unwrap().insert(av);
            }
            let endpoint = {
                let surely_anvil = self.anvil_instance.read().unwrap();
                surely_anvil.as_ref().unwrap().endpoint()
            };
            Url::parse(&endpoint).expect("valid url")
        }

        pub(super) async fn ankr_endpoint(&self) -> Url {
            let is_started: bool = {
                let maybe_ankr = self.ankr_rpc_test.read().unwrap();
                maybe_ankr.is_some()
            };
            if !is_started {
                let ankr_test = AnkrRpcTest::new().await;
                let _ = self.ankr_rpc_test.write().unwrap().insert(ankr_test);
            }
            let endpoint = {
                let surely_ankr = self.ankr_rpc_test.read().unwrap();
                surely_ankr.as_ref().unwrap().url.clone()
            };
            endpoint
        }

        pub fn wallet(&self) -> LocalWallet {
            MnemonicBuilder::<English>::default()
                .phrase(MNEMONIC)
                .build()
                .unwrap()
        }

        pub fn send_native_token(
            &self,
            chain_id: ChainId,
            to_address: ChecksumAddress,
            amount_eth: u64,
        ) {
            let provider = self.eth_api_provider(chain_id);
            let accounts =
                rt::block_on(provider.provider.get_accounts()).expect("get_accounts ok");
            let value = U256::exp10(18) * amount_eth;
            let tx = Eip1559TransactionRequest::new()
                .to(to_address.to_address())
                .value(value)
                .from(accounts[0]);
            let pending_tx = rt::block_on(provider.provider.send_transaction(tx, None))
                .expect("send_transaction ok");
            rt::block_on(pending_tx).expect("pending tx ok");
        }
    }

    impl Default for LocalRpcManager {
        fn default() -> Self {
            Self::new()
        }
    }

    #[async_trait]
    impl RpcManagerI for LocalRpcManager {
        fn eth_rpc_endpoint(&self, chain_id: ChainId) -> Url {
            self.anvil_endpoint(chain_id)
        }

        fn ethers_provider(&self, chain_id: ChainId) -> ProviderType {
            let http_endpoint = self.eth_rpc_endpoint(chain_id);
            Provider::new(Http::new(http_endpoint))
                .interval(Duration::from_millis(POLL_INTERVAL_MS))
        }

        fn eth_gas_oracle(&self, chain_id: ChainId) -> Box<dyn GasOracle> {
            // Don't make requests to remote APIs for tests.
            Box::new(gas_oracle::ProviderOracle::new(
                self.ethers_provider(chain_id),
            ))
        }

        async fn ankr_api_client(
            &self,
        ) -> Result<jsonrpsee::http_client::HttpClient, Error> {
            let url = self.ankr_endpoint().await;
            let client = jsonrpsee::http_client::HttpClientBuilder::default()
                .build(url)
                .map_err(|err| Error::Fatal {
                    error: err.to_string(),
                })?;
            Ok(client)
        }
    }

    impl Debug for LocalRpcManager {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let anvil_instance = self.anvil_instance.read().unwrap();
            let endpoint = anvil_instance.as_ref().map(|a| a.endpoint());
            f.debug_struct("TestAnvilRpcManager")
                .field("anvil_endpoint", &endpoint)
                .finish()
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Add;

    use anyhow::Result;
    use ethers::{
        core::types::U256, providers::PendingTransaction, signers::Signer, types::Address,
    };

    use super::*;
    use crate::protocols::eth::{
        contracts::test_util::TestContractDeployer, LocalRpcManager,
    };

    #[test]
    fn get_block_number() -> Result<()> {
        let rpc_manager = local::LocalRpcManager::new();
        let provider = rpc_manager.eth_api_provider(ChainId::default_dapp_chain());

        let result = provider.proxy_rpc_request("eth_blockNumber", ())?;
        let result: U256 = serde_json::from_value(result)?;

        assert_eq!(result, U256::zero());

        Ok(())
    }

    #[test]
    fn native_token_balance() -> Result<()> {
        let rpc_manager = LocalRpcManager::new();
        let chain_id = ChainId::EthMainnet;
        let provider = rpc_manager.eth_api_provider(chain_id);
        let accounts = rt::block_on(provider.provider.get_accounts())?;

        let balance = provider.native_token_balance(accounts[0].into())?;
        assert_eq!(balance.chain_id, chain_id);
        assert_eq!(balance.display_amount(), "10000");

        Ok(())
    }

    #[test]
    fn sends_native_token() -> Result<()> {
        let chain_id = ChainId::EthMainnet;
        let rpc_manager = LocalRpcManager::new();

        let keychain = Arc::new(Keychain::new());
        let sender_signing = EncryptedSigningKey::random_test_key(&keychain, chain_id)?;

        let rpc_provider =
            rpc_manager.eth_signer_provider(keychain, sender_signing.clone());

        // Send some coin to the address with which we want to test the transfer.
        rpc_manager.send_native_token(chain_id, sender_signing.address, 2);

        let receiver_address: ChecksumAddress = Address::random().into();

        let amount_wei = U256::exp10(18);
        let amount = NativeTokenAmount::new(sender_signing.chain_id, amount_wei);

        let tx_hash = rpc_provider.transfer_native_token(receiver_address, &amount)?;

        rt::block_on(PendingTransaction::new(tx_hash, rpc_provider.provider()))?;

        let balance_receiver = rt::block_on(
            rpc_provider
                .provider()
                .get_balance(receiver_address.to_address(), None),
        )?;
        assert_eq!(balance_receiver, amount_wei);

        Ok(())
    }

    #[test]
    fn sends_fungible_token() -> Result<()> {
        // Deploy ERC20 test contract on Anvil dev node
        let chain_id = ChainId::EthMainnet;
        let contract_deployer = TestContractDeployer::init(chain_id);
        let contract_address = contract_deployer.deploy_fungible_token_test_contract()?;
        let provider = Arc::new(contract_deployer.provider());
        let contract = ERC20Contract::new(contract_address, provider);

        let keychain = Arc::new(Keychain::new());
        let sender_signing = EncryptedSigningKey::random_test_key(&keychain, chain_id)?;

        // Send native token to address that is using our key & tx management for tx fee
        contract_deployer.rpc_manager.send_native_token(
            chain_id,
            sender_signing.address,
            1,
        );

        // Send fungible token to our address
        let amount = U256::exp10(18);
        let call = contract.transfer(sender_signing.address.to_address(), amount);
        // If we don't specify gas here, the tx fails with this weird reason:
        // Error: (code: -32003, message: Out of gas: required gas exceeds allowance: 300000000, data: None)
        // Seems like an Anvil specific issue.
        let call = call.gas(100000);
        let pending_tx = rt::block_on(call.send())?;
        let _receipt = rt::block_on(pending_tx)?;

        // Save the balance of the address that we send the tokens back to prior to transfer with
        // our address.
        let deployer_address: ChecksumAddress =
            contract_deployer.deployer_wallet().address().into();
        let call = contract.balance_of(deployer_address.to_address());
        let prev_balance = rt::block_on(call.call())?;

        // Send back fungible token transfer from our address
        let provider = contract_deployer
            .rpc_manager
            .eth_signer_provider(keychain, sender_signing);
        let tx_hash =
            provider.transfer_fungible_token(deployer_address, "1", contract_address)?;
        let pending_tx = PendingTransaction::new(tx_hash, provider.provider());
        let _receipt = rt::block_on(pending_tx)?;

        // Check that after sending back the tokens the balance is as expected.
        let call = contract.balance_of(deployer_address.to_address());
        let post_balance = rt::block_on(call.call())?;
        assert_eq!(amount.add(prev_balance), post_balance);

        Ok(())
    }

    #[test]
    fn fungible_token_symbol() -> Result<()> {
        // Deploy ERC20 test contract on Anvil dev node
        let chain_id = ChainId::EthMainnet;
        let contract_deployer = TestContractDeployer::init(chain_id);
        let contract_address = contract_deployer.deploy_fungible_token_test_contract()?;

        let rpc_provider = contract_deployer.rpc_manager.eth_api_provider(chain_id);
        let symbol = rpc_provider.fungible_token_symbol(contract_address)?;
        assert_eq!(symbol, "FTT");

        Ok(())
    }
}
