// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::signatures::AsymmetricKey;
use k256::Secp256k1;

pub mod ankr;
mod chain_id;
mod chain_settings;
mod checksum_address;
mod contracts;
pub mod explorer;
mod protocol_data;
mod rpc_provider;
mod signer;
mod signing_key;
mod token;

pub type EthereumAsymmetricKey = AsymmetricKey<Secp256k1>;
pub use chain_id::ChainId;
pub use chain_settings::ChainSettings;
pub use checksum_address::validate_checksum_address;
pub use protocol_data::ProtocolData;
#[cfg(test)]
pub use rpc_provider::anvil::AnvilRpcManager;
pub use rpc_provider::{RpcManager, RpcManagerI, RpcProvider};
pub use signer::Signer;
pub use signing_key::{public_key_to_checksum_address, SigningKey};
pub use token::{FungibleTokenAmount, FungibleTokenBalance, NativeTokenAmount};
