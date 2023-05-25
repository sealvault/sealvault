// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use k256::Secp256k1;

use crate::signatures::AsymmetricKey;

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
mod zksync_gas_oracle;

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
    fetch_token_balances, CommonTokenInfo, CommonTokens, FungibleTokenBalance,
    NFTBalance, TokenBalances,
};

/// Whether we can track a fungible token on a given chain through the token API.
pub fn can_track_token(chain: ChainId) -> bool {
    use crate::protocols::eth::token_api::ankr::AnkrBlockchain;

    // If the chain is supported by Ankr, then we fetch token balances from Ankr which is good
    // because it allows us to automatically detect tokens, but we cannot track tokens other than
    // those supported by Ankr.
    !AnkrBlockchain::supported(chain)
}
