// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use k256::Secp256k1;

use crate::signatures::AsymmetricKey;

// Some names need to be be camel case in ankr for generated code.
#[allow(non_snake_case)]
pub mod ankr;
mod chain_id;
mod chain_settings;
mod checksum_address;
mod contracts;
mod encrypted_signing_key;
pub mod explorer;
pub mod in_page_provider;
mod protocol_data;
mod rpc_provider;
mod signer;
mod token;
mod token_api;

pub type EthereumAsymmetricKey = AsymmetricKey<Secp256k1>;
pub use chain_id::ChainId;
pub use chain_settings::ChainSettings;
pub use checksum_address::ChecksumAddress;
pub use encrypted_signing_key::EncryptedSigningKey;
pub use protocol_data::ProtocolData;
#[cfg(test)]
pub use rpc_provider::local::LocalRpcManager;
pub use rpc_provider::{BaseProvider, RpcManager, RpcManagerI, RpcProvider};
pub use signer::Signer;
pub use token::{FungibleTokenAmount, NativeTokenAmount};
pub use token_api::{
    fetch_token_balances, FungibleTokenBalance, NFTBalance, TokenBalances,
};
