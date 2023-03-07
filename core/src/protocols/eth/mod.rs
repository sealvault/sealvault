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
pub mod explorer;
pub mod in_page_provider;
mod protocol_data;
mod rpc_provider;
mod signer;
mod signing_key;
mod token;

pub type EthereumAsymmetricKey = AsymmetricKey<Secp256k1>;
pub use chain_id::ChainId;
pub use chain_settings::ChainSettings;
pub use checksum_address::ChecksumAddress;
pub use protocol_data::ProtocolData;
#[cfg(test)]
pub use rpc_provider::anvil::AnvilRpcManager;
pub use rpc_provider::{RpcManager, RpcManagerI, RpcProvider};
pub use signer::Signer;
pub use signing_key::SigningKey;
pub use token::{
    FungibleTokenAmount, FungibleTokenBalance, NFTBalance, NativeTokenAmount,
    TokenBalances,
};
