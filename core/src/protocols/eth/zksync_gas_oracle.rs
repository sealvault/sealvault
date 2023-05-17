// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use async_trait::async_trait;
use ethers::{
    addressbook::Address,
    middleware::gas_oracle::{GasOracle, GasOracleError},
    prelude::{Middleware, ProviderError, TransactionRequest, U256},
};

/// A gas oracle that uses the ZkSync specific "zks_estimateFee" RPC method to fetch EIP-1559 fee
/// estimates.
#[derive(Clone, Debug)]
#[must_use]
pub struct ZkSyncGasOracle<M: Middleware> {
    inner: M,
}

impl<M: Middleware> ZkSyncGasOracle<M> {
    pub fn new(middleware: M) -> Self {
        Self { inner: middleware }
    }

    fn map_err(error: ProviderError) -> GasOracleError {
        GasOracleError::ProviderError(Box::new(error))
    }
}

#[async_trait]
impl<M: Middleware> GasOracle for ZkSyncGasOracle<M>
where
    M::Error: 'static,
{
    /// Fetch current gas price estimate
    async fn fetch(&self) -> Result<U256, GasOracleError> {
        self.inner
            .get_gas_price()
            .await
            .map_err(|err| GasOracleError::ProviderError(Box::new(err)))
    }

    /// Fetch current max gas fee and priority fee estimates
    async fn estimate_eip1559_fees(&self) -> Result<(U256, U256), GasOracleError> {
        // Placeholder transaction as we don't have access to the actual transaction in this
        // middleware, but the "zks_estimateFee" method requires one.
        // We don't use the "gas_limit" field from the result, so it doesn't matter what tx we send.
        let from: Address = "0x1111111111111111111111111111111111111111"
            .parse()
            .expect("static ok");
        let to: Address = "0x2222222222222222222222222222222222222222"
            .parse()
            .expect("static ok");
        let tx = TransactionRequest::new()
            .from(from)
            .to(to)
            .data(vec![0xff, 0xff, 0xff]);

        let result: ZkSyncFee = self
            .inner
            .provider()
            .request("zks_estimateFee", vec![tx])
            .await
            .map_err(Self::map_err)?;

        Ok((result.max_fee_per_gas, result.max_priority_fee_per_gas))
    }
}

#[derive(Debug, serde::Deserialize, serde::Serialize)]
struct ZkSyncFee {
    /// zkSync version of EIP1559 maxFeePerGas.
    pub max_fee_per_gas: U256,
    /// zkSync version of EIP1559 maxPriorityFeePerGas.
    pub max_priority_fee_per_gas: U256,
}
