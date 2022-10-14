// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    fmt::{Debug, Formatter},
    sync::Arc,
};

use ethers::{
    core::types::{Address, BlockNumber, TransactionRequest, H256},
    providers::{Http, Middleware, Provider},
    types::BlockId,
};
use serde::Serialize;
use url::Url;

use crate::{
    async_runtime as rt,
    protocols::eth::{
        checksum_address::parse_checksum_address, contracts::ERC20Contract,
        signer::SignerMiddleware, token::FungibleToken, ChainId, FungibleTokenAmount,
        NativeTokenAmount, SigningKey,
    },
    Error,
};

#[derive(Clone, Debug)]
pub struct RpcProvider {
    provider: Provider<Http>,
    chain_id: ChainId,
}

impl RpcProvider {
    pub fn new(chain_id: ChainId, http_endpoint: Url) -> Self {
        let provider = Provider::new(Http::new(http_endpoint));
        Self { provider, chain_id }
    }

    /// Proxy an Ethereum RPC request from an in-page request to the API provider.
    pub fn proxy_rpc_request<T>(
        &self,
        method: &str,
        params: T,
    ) -> Result<serde_json::Value, Error>
    where
        T: Debug + Serialize + Send + Sync,
    {
        rt::block_on(self.proxy_rpc_request_async(method, params))
    }

    pub async fn proxy_rpc_request_async<T>(
        &self,
        method: &str,
        params: T,
    ) -> Result<serde_json::Value, Error>
    where
        T: Debug + Serialize + Send + Sync,
    {
        // Need to make type concrete and convert error
        let res: serde_json::Value = self.provider.request(method, params).await?;
        Ok(res)
    }

    /// Submit a transaction to the network signed with the signing key.
    /// Returns the transaction hash.
    pub fn send_transaction(
        &self,
        signing_key: &SigningKey,
        tx: TransactionRequest,
    ) -> Result<H256, Error> {
        rt::block_on(self.send_transaction_async(signing_key, tx))
    }

    pub async fn send_transaction_async(
        &self,
        signing_key: &SigningKey,
        tx: TransactionRequest,
    ) -> Result<H256, Error> {
        let signer = SignerMiddleware::new(&self.provider, signing_key);
        let pending_tx = signer
            .send_transaction(tx, Some(BlockId::Number(BlockNumber::Latest)))
            .await?;
        let tx_receipt = pending_tx
            .await
            .map_err(tx_failed_with_error)?
            .ok_or_else(tx_failed_error)?;
        Ok(tx_receipt.transaction_hash)
    }

    fn verify_chain_ids(
        &self,
        signing_key: &SigningKey,
        token_chain_id: ChainId,
    ) -> Result<(), Error> {
        if signing_key.chain_id != self.chain_id || signing_key.chain_id != token_chain_id
        {
            Err(Error::Fatal {
                error: format!(
                    "Key, rpc provider and amount chain ids must match. Got {}, {} and {}",
                    signing_key.chain_id, self.chain_id, token_chain_id
                ),
            })
        } else {
            Ok(())
        }
    }

    /// Transfer native token on an Ethereum protocol network.
    /// Returns the transaction hash that can be used to poll for the result.
    pub fn transfer_native_token(
        &self,
        signing_key: &SigningKey,
        to_checksum_address: &str,
        amount: &NativeTokenAmount,
    ) -> Result<String, Error> {
        rt::block_on(self.transfer_native_token_async(
            signing_key,
            to_checksum_address,
            amount,
        ))
    }

    pub async fn transfer_native_token_async(
        &self,
        signing_key: &SigningKey,
        to_checksum_address: &str,
        amount: &NativeTokenAmount,
    ) -> Result<String, Error> {
        self.verify_chain_ids(signing_key, amount.chain_id)?;

        let to_address = parse_checksum_address(to_checksum_address)?;

        // TODO use EIP-1559 once we can get reliable `max_priority_fee_per_gas` estimates on all
        // chains.
        let tx = TransactionRequest::new()
            .to(to_address)
            .value(amount.amount)
            .from(signing_key.address);

        let tx_hash = self.send_transaction_async(signing_key, tx).await?;

        Ok(display_tx_hash(tx_hash))
    }

    pub fn transfer_fungible_token(
        &self,
        signing_key: &SigningKey,
        to_checksum_address: &str,
        amount_decimal: &str,
        contract_checksum_address: &str,
    ) -> Result<String, Error> {
        let future = self.transfer_fungible_token_async(
            signing_key,
            to_checksum_address,
            amount_decimal,
            contract_checksum_address,
        );
        rt::block_on(future)
    }

    pub async fn transfer_fungible_token_async(
        &self,
        signing_key: &SigningKey,
        to_checksum_address: &str,
        amount_decimal: &str,
        contract_checksum_address: &str,
    ) -> Result<String, Error> {
        let contract_address: Address = parse_checksum_address(contract_checksum_address)
            .map_err(|err| match err {
                // Contract address isn't provided by the user
                Error::User { explanation } => Error::Retriable { error: explanation },
                _ => err,
            })?;
        let to_address: Address = parse_checksum_address(to_checksum_address)?;

        let signer = Arc::new(SignerMiddleware::new(&self.provider, signing_key));
        let contract = ERC20Contract::new(contract_address, signer);

        let contract_call = contract.decimals();
        let decimals: u8 =
            contract_call.call().await.map_err(|err| Error::Retriable {
                error: err.to_string(),
            })?;
        let fungible_token =
            FungibleToken::new(self.chain_id, contract_address, decimals);
        let fungible_token_amount =
            FungibleTokenAmount::new_from_decimal(fungible_token, amount_decimal)?;

        let contract_call = contract.transfer(to_address, fungible_token_amount.amount);
        let pending_tx = contract_call.send().await.map_err(|err| Error::Retriable {
            error: err.to_string(),
        })?;
        let tx_receipt = pending_tx
            .await
            .map_err(tx_failed_with_error)?
            .ok_or_else(tx_failed_error)?;
        Ok(display_tx_hash(tx_receipt.transaction_hash))
    }

    /// Fetch the native token balance for an address.
    pub fn native_token_balance(
        &self,
        address: &str,
    ) -> Result<NativeTokenAmount, Error> {
        rt::block_on(self.native_token_balance_async(address))
    }

    pub async fn native_token_balance_async(
        &self,
        address: &str,
    ) -> Result<NativeTokenAmount, Error> {
        let address = address.parse::<Address>().map_err(|err| Error::Retriable {
            error: err.to_string(),
        })?;
        let block_id: Option<BlockId> = Some(BlockNumber::Latest.into());
        let balance = self.provider.get_balance(address, block_id).await?;
        let amount = NativeTokenAmount::new(self.chain_id, balance);
        Ok(amount)
    }
}

/// A trait to let us inject dynamic Anvil url at test time.
pub trait RpcManagerI: Debug + Send + Sync {
    fn eth_api_provider(&self, chain_id: ChainId) -> RpcProvider;
}

pub struct RpcManager {}

impl RpcManager {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for RpcManager {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for RpcManager {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RpcManagerImpl").finish()
    }
}

impl RpcManagerI for RpcManager {
    fn eth_api_provider(&self, chain_id: ChainId) -> RpcProvider {
        let http_endpoint = chain_id.http_rpc_endpoint();
        RpcProvider::new(chain_id, http_endpoint)
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
pub mod anvil {
    use std::{
        fmt::Formatter,
        sync::{Arc, RwLock},
    };

    use ethers::core::utils::{Anvil, AnvilInstance};

    use super::*;

    pub struct AnvilRpcManager {
        // Lazy initialized Anvil instance.
        anvil_instance: Arc<RwLock<Option<AnvilInstance>>>,
    }

    impl AnvilRpcManager {
        pub fn new() -> Self {
            let anvil_instance = Arc::new(RwLock::new(None));
            Self { anvil_instance }
        }

        fn anvil_endpoint(&self) -> Url {
            let is_started: bool = {
                let maybe_anvil = self.anvil_instance.read().unwrap();
                maybe_anvil.is_some()
            };
            if !is_started {
                let av = Anvil::new().spawn();
                let _ = self.anvil_instance.write().unwrap().insert(av);
            }
            let endpoint = {
                let surely_anvil = self.anvil_instance.read().unwrap();
                surely_anvil.as_ref().unwrap().endpoint()
            };
            Url::parse(&*endpoint).expect("valid url")
        }
    }

    impl Default for AnvilRpcManager {
        fn default() -> Self {
            Self::new()
        }
    }

    impl RpcManagerI for AnvilRpcManager {
        fn eth_api_provider(&self, chain_id: ChainId) -> RpcProvider {
            let http_endpoint = self.anvil_endpoint();
            RpcProvider::new(chain_id, http_endpoint)
        }
    }

    impl Debug for AnvilRpcManager {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let anvil_endpoint = self.anvil_endpoint();
            f.debug_struct("TestAnvilRpcManager")
                .field("anvil_endpoint", &anvil_endpoint)
                .finish()
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Add;

    use anyhow::Result;
    use ethers::{
        core::{types::U256, utils::Anvil},
        providers::{PendingTransaction, Provider},
        signers::Signer,
        utils::to_checksum,
    };

    use super::*;
    use crate::protocols::{
        eth::{
            contracts::test_util::TestContractDeployer, signing_key::checksum_address,
            EthereumAsymmetricKey,
        },
        ChecksumAddress,
    };

    #[test]
    fn get_block_number() -> Result<()> {
        let rpc_manager = anvil::AnvilRpcManager::new();
        let provider = rpc_manager.eth_api_provider(ChainId::default_dapp_chain());

        let result = provider.proxy_rpc_request("eth_blockNumber", ())?;
        let result: U256 = serde_json::from_value(result)?;

        assert_eq!(result, U256::zero());

        Ok(())
    }

    #[test]
    fn native_token_balance() -> Result<()> {
        let rpc_manager = anvil::AnvilRpcManager::new();
        let chain_id = ChainId::EthMainnet;
        let provider = rpc_manager.eth_api_provider(chain_id);
        let accounts = rt::block_on(provider.provider.get_accounts())?;

        let address = checksum_address(&accounts[0]);
        let balance = provider.native_token_balance(&*address)?;
        assert_eq!(balance.chain_id, chain_id);
        assert_eq!(balance.display_amount(), "10000");

        Ok(())
    }

    #[test]
    fn sends_native_token() -> Result<()> {
        let poll_interval = std::time::Duration::from_millis(10);
        let chain_id = ChainId::EthMainnet;
        let anvil = Anvil::new().chain_id(chain_id as u64).spawn();
        let anvil_provider =
            Provider::<Http>::try_from(anvil.endpoint())?.interval(poll_interval);

        let amount_wei = U256::exp10(18);

        let sender_key = EthereumAsymmetricKey::random()?;
        let sender_signing = SigningKey::new(sender_key, ChainId::EthMainnet)?;

        // Send some coin to the address with which we want to test the transfer.
        let accounts = rt::block_on(anvil_provider.get_accounts())?;
        let tx = TransactionRequest::new()
            .to(sender_signing.address)
            // Headroom for gas fees
            .value(amount_wei.saturating_mul(2.into()))
            .from(accounts[0]);
        let pending_tx = rt::block_on(anvil_provider.send_transaction(tx, None))?;
        // Await the returned pending transaction to make sure it's completed before we move on.
        rt::block_on(pending_tx)?;

        let receiver_key = EthereumAsymmetricKey::random()?;
        let receiver_signing = SigningKey::new(receiver_key, ChainId::EthMainnet)?;

        let receiver_checksum = receiver_signing.checksum_address();
        let amount = NativeTokenAmount::new(sender_signing.chain_id, amount_wei);

        let rpc_provider = RpcProvider::new(
            sender_signing.chain_id,
            Url::parse(&*anvil.endpoint()).unwrap(),
        );
        let tx_hash = rpc_provider.transfer_native_token(
            &sender_signing,
            &receiver_checksum,
            &amount,
        )?;

        rt::block_on(
            PendingTransaction::new(tx_hash.parse()?, &anvil_provider)
                .interval(poll_interval),
        )?;

        let balance_receiver =
            rt::block_on(anvil_provider.get_balance(receiver_signing.address, None))?;
        assert_eq!(balance_receiver, amount_wei);

        Ok(())
    }

    #[test]
    fn sends_fungible_token() -> Result<()> {
        // Deploy ERC20 test contract on Anvil dev node
        let chain_id = ChainId::EthMainnet;
        let contract_deployer = TestContractDeployer::init(chain_id);
        let contract_address =
            rt::block_on(contract_deployer.deploy_fungible_token_test_contract())?;
        let deployer_wallet = contract_deployer.deployer_wallet();
        let provider = Arc::new(contract_deployer.provider());
        let contract = ERC20Contract::new(contract_address, provider.clone());

        let sender_key = EthereumAsymmetricKey::random()?;
        let sender_signing = SigningKey::new(sender_key, ChainId::EthMainnet)?;

        // Send native token to address that is using our key & tx management for tx fee
        let tx = TransactionRequest::new()
            .to(sender_signing.address)
            // Headroom for gas fees
            .value(U256::exp10(18))
            .from(deployer_wallet.address());
        let pending_tx = rt::block_on(provider.send_transaction(tx, None))?;
        // Await the returned pending transaction to make sure it's completed before we move on.
        rt::block_on(pending_tx)?;

        // Send fungible token to our address
        let amount = U256::exp10(18);
        let call = contract.transfer(sender_signing.address, amount);
        // If we don't specify gas here, the tx fails with this weird reason:
        // Error: (code: -32003, message: Out of gas: required gas exceeds allowance: 300000000, data: None)
        // Seems like an Anvil specific issue.
        let call = call.gas(100000);
        let pending_tx = rt::block_on(call.send())?;
        let _receipt = rt::block_on(pending_tx)?;

        // Save the balance of the address that we send the tokens back to prior to transfer with
        // our address.
        let call = contract.balance_of(deployer_wallet.address());
        let prev_balance = rt::block_on(call.call())?;

        // Send back fungible token transfer from our address
        let rpc_provider = RpcProvider::new(
            sender_signing.chain_id,
            Url::parse(&*contract_deployer.endpoint()).unwrap(),
        );
        let to_checksum_adress = to_checksum(&deployer_wallet.address(), None);
        let contract_checksum_address = to_checksum(&contract_address, None);
        let tx_hash = rpc_provider.transfer_fungible_token(
            &sender_signing,
            &to_checksum_adress,
            "1",
            &contract_checksum_address,
        )?;
        let tx_hash: H256 = tx_hash.parse().unwrap();
        let pending_tx = PendingTransaction::new(tx_hash, &provider);
        let _receipt = rt::block_on(pending_tx)?;

        // Check that after sending back the tokens the balance is as expected.
        let call = contract.balance_of(deployer_wallet.address());
        let post_balance = rt::block_on(call.call())?;
        assert_eq!(amount.add(prev_balance), post_balance);

        Ok(())
    }
}
