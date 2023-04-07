// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
use ethers::core::{
    abi::ethereum_types::H64,
    types::{
        serde_helpers::{
            deserialize_number, lenient_block_number, lenient_block_number_seq,
        },
        transaction::eip712::TypedData,
        Address, BlockId, BlockNumber, Bytes, Filter, GethDebugTracingOptions,
        TransactionRequest, TxHash, H256, U256,
    },
};
use jsonrpsee::core::Serialize;
use serde::Deserialize;
use serde_json::value::RawValue;

use crate::Error;

/// Represents an EIP-1193 in-page request.
/// Based on Anvil's [InPageRequest](https://github.com/foundry-rs/foundry/blob/1d9a34ecfe265d49b4237c9eb670d5aec389b646/anvil/core/src/eth/mod.rs)
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, strum_macros::Display)]
#[serde(tag = "method", content = "params")]
pub enum InPageRequest {
    // Wallet specific methods
    /// https://docs.metamask.io/guide/signing-data.html#personal-sign
    #[serde(rename = "personal_sign")]
    PersonalSign(Bytes, Address, #[serde(default)] Option<String>),

    /// https://docs.metamask.io/guide/rpc-api.html#wallet-addethereumchain
    #[serde(rename = "wallet_addEthereumChain", with = "sequence_len_one")]
    WalletAddEthereumChain(AddEthereumChainParameter),

    /// https://docs.metamask.io/guide/rpc-api.html#wallet-switchethereumchain
    #[serde(rename = "wallet_switchEthereumChain", with = "sequence_len_one")]
    WalletSwitchEthereumChain(SwitchEthereumChainParameter),

    /// https://docs.metamask.io/guide/rpc-api.html#unrestricted-methods
    #[serde(rename = "wallet_watchAsset")]
    WalletWatchAsset(WatchAssetParams),

    // Ethereum RPC methods
    #[serde(rename = "web3_clientVersion", with = "empty_params")]
    Web3ClientVersion(()),

    #[serde(rename = "web3_sha3", with = "sequence_len_one")]
    Web3Sha3(Bytes),

    #[serde(rename = "eth_chainId", with = "empty_params")]
    EthChainId(()),

    #[serde(rename = "eth_networkId", alias = "net_version", with = "empty_params")]
    EthNetworkId(()),

    #[serde(rename = "net_listening", with = "empty_params")]
    NetListening(()),

    #[serde(rename = "eth_gasPrice", with = "empty_params")]
    EthGasPrice(()),

    #[serde(rename = "eth_maxPriorityFeePerGas", with = "empty_params")]
    EthMaxPriorityFeePerGas(()),

    #[serde(
        rename = "eth_accounts",
        alias = "eth_requestAccounts",
        with = "empty_params"
    )]
    EthAccounts(()),

    #[serde(rename = "eth_blockNumber", with = "empty_params")]
    EthBlockNumber(()),

    #[serde(rename = "eth_getBalance")]
    EthGetBalance(Address, Option<BlockId>),

    #[serde(rename = "eth_getStorageAt")]
    EthGetStorageAt(Address, U256, Option<BlockId>),

    #[serde(rename = "eth_getBlockByHash")]
    EthGetBlockByHash(H256, bool),

    #[serde(rename = "eth_getBlockByNumber")]
    EthGetBlockByNumber(
        #[serde(deserialize_with = "lenient_block_number")] BlockNumber,
        bool,
    ),

    #[serde(rename = "eth_getTransactionCount")]
    EthGetTransactionCount(Address, Option<BlockId>),

    #[serde(
        rename = "eth_getBlockTransactionCountByHash",
        with = "sequence_len_one"
    )]
    EthGetTransactionCountByHash(H256),

    #[serde(
        rename = "eth_getBlockTransactionCountByNumber",
        deserialize_with = "lenient_block_number_seq"
    )]
    EthGetTransactionCountByNumber(BlockNumber),

    #[serde(rename = "eth_getUncleCountByBlockHash", with = "sequence_len_one")]
    EthGetUnclesCountByHash(H256),

    #[serde(
        rename = "eth_getUncleCountByBlockNumber",
        deserialize_with = "lenient_block_number_seq"
    )]
    EthGetUnclesCountByNumber(BlockNumber),

    #[serde(rename = "eth_getCode")]
    EthGetCodeAt(Address, Option<BlockId>),

    /// Returns the account and storage values of the specified account including the Merkle-proof.
    /// This call can be used to verify that the data you are pulling from is not tampered with.
    #[serde(rename = "eth_getProof")]
    EthGetProof(Address, Vec<H256>, Option<BlockId>),

    /// The sign method calculates an Ethereum specific signature with:
    #[serde(rename = "eth_sign")]
    EthSign(Address, Bytes),

    /// Signs data via [EIP-712](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-712.md).
    #[serde(rename = "eth_signTypedData")]
    EthSignTypedData(Address, serde_json::Value),

    /// Signs data via [EIP-712](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-712.md).
    #[serde(rename = "eth_signTypedData_v3")]
    EthSignTypedDataV3(Address, serde_json::Value),

    /// Signs data via [EIP-712](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-712.md), and includes full support of arrays and recursive data structures.
    #[serde(rename = "eth_signTypedData_v4")]
    EthSignTypedDataV4(Address, TypedData),

    #[serde(rename = "eth_sendTransaction", with = "sequence_len_one")]
    EthSendTransaction(TransactionRequest),

    #[serde(rename = "eth_sendRawTransaction", with = "sequence_len_one")]
    EthSendRawTransaction(Bytes),

    #[serde(rename = "eth_call")]
    EthCall(TransactionRequest, #[serde(default)] Option<BlockId>),

    #[serde(rename = "eth_createAccessList")]
    EthCreateAccessList(TransactionRequest, #[serde(default)] Option<BlockId>),

    #[serde(rename = "eth_estimateGas")]
    EthEstimateGas(TransactionRequest, #[serde(default)] Option<BlockId>),

    #[serde(rename = "eth_getTransactionByHash", with = "sequence_len_one")]
    EthGetTransactionByHash(TxHash),

    #[serde(rename = "eth_getTransactionByBlockHashAndIndex")]
    EthGetTransactionByBlockHashAndIndex(TxHash, serde_json::Value),

    #[serde(rename = "eth_getTransactionByBlockNumberAndIndex")]
    EthGetTransactionByBlockNumberAndIndex(
        #[serde(deserialize_with = "lenient_block_number")] BlockNumber,
        serde_json::Value,
    ),

    #[serde(rename = "eth_getTransactionReceipt", with = "sequence_len_one")]
    EthGetTransactionReceipt(H256),

    #[serde(rename = "eth_getUncleByBlockHashAndIndex")]
    EthGetUncleByBlockHashAndIndex(H256, serde_json::Value),

    #[serde(rename = "eth_getUncleByBlockNumberAndIndex")]
    EthGetUncleByBlockNumberAndIndex(
        #[serde(deserialize_with = "lenient_block_number")] BlockNumber,
        serde_json::Value,
    ),

    #[serde(rename = "eth_getLogs", with = "sequence_len_one")]
    EthGetLogs(Filter),

    /// Creates a filter object, based on filter options, to notify when the state changes (logs).
    #[serde(rename = "eth_newFilter", with = "sequence_len_one")]
    EthNewFilter(Filter),

    /// Polling method for a filter, which returns an array of logs which occurred since last poll.
    #[serde(rename = "eth_getFilterChanges", with = "sequence_len_one")]
    EthGetFilterChanges(String),

    /// Creates a filter in the node, to notify when a new block arrives.
    /// To check if the state has changed, call `eth_getFilterChanges`.
    #[serde(rename = "eth_newBlockFilter", with = "empty_params")]
    EthNewBlockFilter(()),

    /// Creates a filter in the node, to notify when new pending transactions arrive.
    /// To check if the state has changed, call `eth_getFilterChanges`.
    #[serde(rename = "eth_newPendingTransactionFilter", with = "empty_params")]
    EthNewPendingTransactionFilter(()),

    /// Returns an array of all logs matching filter with given id.
    #[serde(rename = "eth_getFilterLogs", with = "sequence_len_one")]
    EthGetFilterLogs(String),

    /// Removes the filter, returns true if the filter was installed
    #[serde(rename = "eth_uninstallFilter", with = "sequence_len_one")]
    EthUninstallFilter(String),

    #[serde(rename = "eth_getWork", with = "empty_params")]
    EthGetWork(()),

    #[serde(rename = "eth_submitWork")]
    EthSubmitWork(H64, H256, H256),

    #[serde(rename = "eth_submitHashrate")]
    EthSubmitHashRate(U256, H256),

    #[serde(rename = "eth_feeHistory")]
    EthFeeHistory(
        #[serde(deserialize_with = "deserialize_number")] U256,
        BlockNumber,
        #[serde(default)] Vec<f64>,
    ),

    #[serde(rename = "eth_syncing", with = "empty_params")]
    EthSyncing(()),

    /// geth's `debug_traceTransaction`  endpoint
    #[serde(rename = "debug_traceTransaction")]
    DebugTraceTransaction(H256, #[serde(default)] GethDebugTracingOptions),

    /// geth's `debug_traceCall`  endpoint
    #[serde(rename = "debug_traceCall")]
    DebugTraceCall(
        TransactionRequest,
        #[serde(default)] Option<BlockId>,
        #[serde(default)] GethDebugTracingOptions,
    ),

    /// Trace transaction endpoint for parity's `trace_transaction`
    #[serde(rename = "trace_transaction", with = "sequence_len_one")]
    TraceTransaction(H256),

    /// Trace transaction endpoint for parity's `trace_block`
    #[serde(rename = "trace_block", deserialize_with = "lenient_block_number_seq")]
    TraceBlock(BlockNumber),

    /// Returns the number of transactions currently pending for inclusion in the next block(s), as
    /// well as the ones that are being scheduled for future execution only.
    /// Ref: [Here](https://geth.ethereum.org/docs/rpc/ns-txpool#txpool_status)
    #[serde(rename = "txpool_status", with = "empty_params")]
    TxPoolStatus(()),

    /// Returns a summary of all the transactions currently pending for inclusion in the next
    /// block(s), as well as the ones that are being scheduled for future execution only.
    /// Ref: [Here](https://geth.ethereum.org/docs/rpc/ns-txpool#txpool_inspect)
    #[serde(rename = "txpool_inspect", with = "empty_params")]
    TxPoolInspect(()),

    /// Returns the details of all transactions currently pending for inclusion in the next
    /// block(s), as well as the ones that are being scheduled for future execution only.
    /// Ref: [Here](https://geth.ethereum.org/docs/rpc/ns-txpool#txpool_content)
    #[serde(rename = "txpool_content", with = "empty_params")]
    TxPoolContent(()),
}

impl InPageRequest {
    pub fn allow_proxy(&self) -> bool {
        matches!(
            *self,
            InPageRequest::NetListening(..)
                | InPageRequest::EthGasPrice(..)
                | InPageRequest::EthMaxPriorityFeePerGas(..)
                | InPageRequest::EthBlockNumber(..)
                | InPageRequest::EthGetBalance(..)
                | InPageRequest::EthGetStorageAt(..)
                | InPageRequest::EthGetBlockByHash(..)
                | InPageRequest::EthGetBlockByNumber(..)
                | InPageRequest::EthGetTransactionCount(..)
                | InPageRequest::EthGetTransactionCountByHash(..)
                | InPageRequest::EthGetTransactionCountByNumber(..)
                | InPageRequest::EthGetUnclesCountByHash(..)
                | InPageRequest::EthGetUnclesCountByNumber(..)
                | InPageRequest::EthGetCodeAt(..)
                | InPageRequest::EthGetProof(..)
                | InPageRequest::EthSendRawTransaction(..)
                | InPageRequest::EthCall(..)
                | InPageRequest::EthCreateAccessList(..)
                | InPageRequest::EthEstimateGas(..)
                | InPageRequest::EthGetTransactionByHash(..)
                | InPageRequest::EthGetTransactionByBlockHashAndIndex(..)
                | InPageRequest::EthGetTransactionByBlockNumberAndIndex(..)
                | InPageRequest::EthGetTransactionReceipt(..)
                | InPageRequest::EthGetUncleByBlockHashAndIndex(..)
                | InPageRequest::EthGetUncleByBlockNumberAndIndex(..)
                | InPageRequest::EthGetLogs(..)
                | InPageRequest::EthNewFilter(..)
                | InPageRequest::EthGetFilterChanges(..)
                | InPageRequest::EthNewBlockFilter(..)
                | InPageRequest::EthNewPendingTransactionFilter(..)
                | InPageRequest::EthGetFilterLogs(..)
                | InPageRequest::EthUninstallFilter(..)
                | InPageRequest::EthGetWork(..)
                | InPageRequest::EthSubmitHashRate(..)
                | InPageRequest::EthFeeHistory(..)
                | InPageRequest::EthSyncing(..)
                | InPageRequest::DebugTraceTransaction(..)
                | InPageRequest::DebugTraceCall(..)
                | InPageRequest::TraceTransaction(..)
                | InPageRequest::TraceBlock(..)
                | InPageRequest::TxPoolStatus(..)
                | InPageRequest::TxPoolInspect(..)
                | InPageRequest::TxPoolContent(..)
        )
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct InPageRequestParams {
    pub method: String,
    pub params: Box<RawValue>,
}

impl TryFrom<InPageRequest> for InPageRequestParams {
    type Error = Error;

    fn try_from(value: InPageRequest) -> Result<Self, Self::Error> {
        fn handle_error(_: serde_json::Error) -> Error {
            Error::Fatal {
                error: "Failed to deserialize InPageRequest".to_string(),
            }
        }

        let json = serde_json::to_value(value).map_err(handle_error)?;
        serde_json::from_value(json).map_err(handle_error)
    }
}

/// Incomplete because we only care about the chain_id param.
/// From https://docs.metamask.io/guide/rpc-api.html#wallet-addethereumchain
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AddEthereumChainParameter {
    pub chain_id: String, // A 0x-prefixed hexadecimal string
}

/// From https://docs.metamask.io/guide/rpc-api.html#wallet-switchethereumchain
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SwitchEthereumChainParameter {
    pub chain_id: String, // A 0x-prefixed hexadecimal string
}

/// From https://docs.metamask.io/guide/rpc-api.html#unrestricted-methods
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WatchAssetParams {
    #[serde(rename = "type")]
    pub type_: WatchAssetType,
    pub options: WatchAssetOptions,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum WatchAssetType {
    Erc20,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WatchAssetOptions {
    /// The address of the token contract.
    pub address: String,
    /// A ticker symbol or shorthand, up to 11 characters
    pub symbol: Option<String>,
    /// The number of token decimals.
    pub decimals: Option<u8>,
    /// A string url of the token logo
    pub image: Option<String>,
}

/// From [Foundry](https://github.com/foundry-rs/foundry/blob/1d9a34ecfe265d49b4237c9eb670d5aec389b646/anvil/core/src/eth/serde_helpers.rs)
mod sequence_len_one {
    use serde::{
        de::DeserializeOwned, ser::SerializeSeq, Deserialize, Deserializer, Serialize,
        Serializer,
    };

    pub fn serialize<S, T>(val: &T, s: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: Serialize,
    {
        let mut seq = s.serialize_seq(Some(1))?;
        seq.serialize_element(val)?;
        seq.end()
    }

    pub fn deserialize<'de, T, D>(d: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: DeserializeOwned,
    {
        let mut seq = Vec::<T>::deserialize(d)?;
        if seq.len() != 1 {
            return Err(serde::de::Error::custom(format!(
                "expected params sequence with length 1 but got {}",
                seq.len()
            )));
        }
        Ok(seq.remove(0))
    }
}

/// A module that deserializes `[]` optionally
/// Based on [Foundry](https://github.com/foundry-rs/foundry/blob/1d9a34ecfe265d49b4237c9eb670d5aec389b646/anvil/core/src/eth/serde_helpers.rs)
mod empty_params {
    use serde::{ser::SerializeSeq, Deserialize, Deserializer, Serializer};

    // Serialize an empty sequence
    pub fn serialize<S>(_: &(), s: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let seq = s.serialize_seq(Some(0))?;
        seq.end()
    }

    pub fn deserialize<'de, D>(d: D) -> Result<(), D::Error>
    where
        D: Deserializer<'de>,
    {
        let seq = Option::<Vec<()>>::deserialize(d)?.unwrap_or_default();
        if !seq.is_empty() {
            return Err(serde::de::Error::custom(format!(
                "expected params sequence with length 0 but got {}",
                seq.len()
            )));
        }
        Ok(())
    }
}

/// Based on [Foundry](https://github.com/foundry-rs/foundry/blob/1d9a34ecfe265d49b4237c9eb670d5aec389b646/anvil/core/src/eth/mod.rs)
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_web3_client_version() {
        let s = r#"{"method":"web3_clientVersion","params":[]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let req = serde_json::from_value::<InPageRequest>(value).unwrap();
        let s_prime = serde_json::to_string(&req).unwrap();
        assert_eq!(s, s_prime);
    }

    #[test]
    fn test_web3_sha3() {
        let s = r#"{"method":"web3_sha3","params":["0x68656c6c6f20776f726c64"]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let req = serde_json::from_value::<InPageRequest>(value).unwrap();
        let s_prime = serde_json::to_string(&req).unwrap();
        assert_eq!(s, s_prime);
    }

    #[test]
    fn test_eth_accounts() {
        let s = r#"{"method": "eth_accounts", "params":[]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_network_id() {
        let s = r#"{"method": "eth_networkId", "params":[]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_get_proof() {
        let s = r#"{"method":"eth_getProof","params":["0x7f0d15c7faae65896648c8273b6d7e43f58fa842",["0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"],"latest"]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let req = serde_json::from_value::<InPageRequest>(value).unwrap();
        let s_prime = serde_json::to_string(&req).unwrap();
        assert_eq!(s, s_prime);
    }

    #[test]
    fn test_eth_chain_id() {
        let s = r#"{"method": "eth_chainId", "params":[]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_net_listening() {
        let s = r#"{"method": "net_listening", "params":[]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_block_number() {
        let s = r#"{"method": "eth_blockNumber", "params":[]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_max_priority_fee() {
        let s = r#"{"method": "eth_maxPriorityFeePerGas", "params":[]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_syncing() {
        let s = r#"{"method": "eth_syncing", "params":[]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_uncle_count_by_block_hash() {
        let s = r#"{"jsonrpc":"2.0","method":"eth_getUncleCountByBlockHash","params":["0x4a3b0fce2cb9707b0baa68640cf2fe858c8bb4121b2a8cb904ff369d38a560ff"]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_block_tx_count_by_block_hash() {
        let s = r#"{"jsonrpc":"2.0","method":"eth_getBlockTransactionCountByHash","params":["0x4a3b0fce2cb9707b0baa68640cf2fe858c8bb4121b2a8cb904ff369d38a560ff"]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_get_logs() {
        let s = r#"{"jsonrpc":"2.0","method":"eth_getLogs","params":[{"topics":["0x000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b"]}],"id":74}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_new_filter() {
        let s = r#"{"method": "eth_newFilter", "params": [{"topics":["0x000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b"]}],"id":73}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_serde_debug_trace_transaction() {
        let s = r#"{"method": "debug_traceTransaction", "params": ["0x4a3b0fce2cb9707b0baa68640cf2fe858c8bb4121b2a8cb904ff369d38a560ff"]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();

        let s = r#"{"method": "debug_traceTransaction", "params": ["0x4a3b0fce2cb9707b0baa68640cf2fe858c8bb4121b2a8cb904ff369d38a560ff", {}]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();

        let s = r#"{"method": "debug_traceTransaction", "params": ["0x4a3b0fce2cb9707b0baa68640cf2fe858c8bb4121b2a8cb904ff369d38a560ff", {"disableStorage": true}]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_serde_debug_trace_call() {
        let s = r#"{"method": "debug_traceCall", "params": [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();

        let s = r#"{"method": "debug_traceCall", "params": [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}, { "blockNumber": "latest" }]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();

        let s = r#"{"method": "debug_traceCall", "params": [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}, { "blockNumber": "0x0" }]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();

        let s = r#"{"method": "debug_traceCall", "params": [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}, { "blockHash": "0xd4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3" }]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();

        let s = r#"{"method": "debug_traceCall", "params": [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}, { "blockNumber": "0x0" }, {"disableStorage": true}]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_serde_eth_storage() {
        let s = r#"{"method": "eth_getStorageAt", "params": ["0x295a70b2de5e3953354a6a8344e616ed314d7251", "0x0", "latest"]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_call() {
        let s = r#"{"method": "eth_call", "params":  [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"},"latest"]}"#;
        let _req = serde_json::from_str::<InPageRequest>(s).unwrap();

        let s = r#"{"method": "eth_call", "params":  [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}]}"#;
        let _req = serde_json::from_str::<InPageRequest>(s).unwrap();

        let s = r#"{"method": "eth_call", "params":  [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}, { "blockNumber": "latest" }]}"#;
        let _req = serde_json::from_str::<InPageRequest>(s).unwrap();

        let s = r#"{"method": "eth_call", "params":  [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}, { "blockNumber": "0x0" }]}"#;
        let _req = serde_json::from_str::<InPageRequest>(s).unwrap();

        let s = r#"{"method": "eth_call", "params":  [{"data":"0xcfae3217","from":"0xd84de507f3fada7df80908082d3239466db55a71","to":"0xcbe828fdc46e3b1c351ec90b1a5e7d9742c0398d"}, { "blockHash": "0xd4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3" }]}"#;
        let _req = serde_json::from_str::<InPageRequest>(s).unwrap();
    }

    #[test]
    fn test_serde_eth_balance() {
        let s = r#"{"method": "eth_getBalance", "params": ["0x295a70b2de5e3953354a6a8344e616ed314d7251", "latest"]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();

        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_serde_eth_block_by_number() {
        let s = r#"{"method": "eth_getBlockByNumber", "params": ["0x0", true]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
        let s = r#"{"method": "eth_getBlockByNumber", "params": ["latest", true]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
        let s = r#"{"method": "eth_getBlockByNumber", "params": ["earliest", true]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
        let s = r#"{"method": "eth_getBlockByNumber", "params": ["pending", true]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();

        // this case deviates from the spec, but we're supporting this for legacy reasons: <https://github.com/foundry-rs/foundry/issues/1868>
        let s = r#"{"method": "eth_getBlockByNumber", "params": [0, true]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_eth_sign_typed_data() {
        let s = r#"{"method":"eth_signTypedData_v4","params":["0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826", {"types":{"EIP712Domain":[{"name":"name","type":"string"},{"name":"version","type":"string"},{"name":"chainId","type":"uint256"},{"name":"verifyingContract","type":"address"}],"Person":[{"name":"name","type":"string"},{"name":"wallet","type":"address"}],"Mail":[{"name":"from","type":"Person"},{"name":"to","type":"Person"},{"name":"contents","type":"string"}]},"primaryType":"Mail","domain":{"name":"Ether Mail","version":"1","chainId":1,"verifyingContract":"0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC"},"message":{"from":{"name":"Cow","wallet":"0xCD2a3d9F938E13CD947Ec05AbC7FE734Df8DD826"},"to":{"name":"Bob","wallet":"0xbBbBBBBbbBBBbbbBbbBbbbbBBbBbbbbBbBbbBBbB"},"contents":"Hello, Bob!"}}]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_add_eth_chain() {
        let s = r#"{"jsonrpc":"2.0","id":"e557bea9-32c6-4201-b42c-7ae433ba2986","method":"wallet_addEthereumChain","params":[{"chainId":"0x1"}]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }

    #[test]
    fn test_switch_eth_chain() {
        let s = r#"{"jsonrpc":"2.0","id":"e557bea9-32c6-4201-b42c-7ae433ba2986","method":"wallet_switchEthereumChain","params":[{"chainId":"0x1"}]}"#;
        let value: serde_json::Value = serde_json::from_str(s).unwrap();
        let _req = serde_json::from_value::<InPageRequest>(value).unwrap();
    }
}
