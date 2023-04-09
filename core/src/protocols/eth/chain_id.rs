// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use ethers::{
    core::{
        types::{U256, U64},
        utils::parse_units,
    },
    types::Chain,
    utils::ParseUnits,
};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use serde::{Deserialize, Serialize};
use strum_macros::{EnumIter, EnumString};
use url::Url;

use crate::{
    protocols::eth::{
        chain_settings::ChainSettings, token::NativeToken, NativeTokenAmount,
    },
    Error,
};

#[derive(
    Copy,
    Clone,
    Debug,
    PartialEq,
    Eq,
    Hash,
    EnumIter,
    EnumString,
    FromPrimitive,
    strum_macros::Display,
    Serialize,
    Deserialize,
)]
#[strum(serialize_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum ChainId {
    EthMainnet = 1,
    EthGoerli = 5,

    PolygonMainnet = 137,
    PolygonMumbai = 80001,

    FilecoinHyperspaceTestnet = 3141,
}

impl ChainId {
    pub fn default_dapp_chain() -> Self {
        Self::PolygonMainnet
    }

    pub fn default_wallet_chain() -> Self {
        // Important to match dapp chain because users will want to fund the wallet with tokens
        // first that they use for dapps.
        Self::default_dapp_chain()
    }

    // Does not necessarily match chain id
    // We return string because it's only used to support a legacy MetaMask api that needs string.
    pub fn network_version(&self) -> String {
        match *self {
            Self::EthMainnet => "1",
            Self::EthGoerli => "5",

            Self::PolygonMainnet => "137",
            Self::PolygonMumbai => "80001",

            Self::FilecoinHyperspaceTestnet => "3141",
        }
        .into()
    }

    /// Display chain id as hex string prefixed with 0x, eg "0x89"
    pub fn display_hex(self) -> String {
        let hex_chain_id: U64 = self.into();
        let mut hex_chain_id = serde_json::to_string(&hex_chain_id)
            .expect("serde_json::Value can be always deserialized");

        // Remove first and last quotation marks from json serialization
        hex_chain_id.remove(0);
        hex_chain_id.pop();

        hex_chain_id
    }

    pub fn display_name(&self) -> String {
        match *self {
            Self::EthMainnet => "Ethereum",
            Self::EthGoerli => "Ethereum Goerli Testnet",

            Self::PolygonMainnet => "Polygon PoS",
            Self::PolygonMumbai => "Polygon PoS Mumbai Testnet",

            Self::FilecoinHyperspaceTestnet => "Filecoin Hyperspace Testnet",
        }
        .into()
    }

    pub fn is_test_net(&self) -> bool {
        match *self {
            Self::EthMainnet => false,
            Self::EthGoerli => true,

            Self::PolygonMainnet => false,
            Self::PolygonMumbai => true,

            Self::FilecoinHyperspaceTestnet => true,
        }
    }

    pub fn native_token(&self) -> NativeToken {
        match *self {
            Self::EthMainnet => NativeToken::Eth,
            Self::EthGoerli => NativeToken::Eth,

            Self::PolygonMainnet => NativeToken::Matic,
            Self::PolygonMumbai => NativeToken::Matic,

            Self::FilecoinHyperspaceTestnet => NativeToken::TestFil,
        }
    }

    pub fn http_rpc_endpoint(&self) -> Url {
        let raw_url = match *self {
            ChainId::EthMainnet => "https://rpc.ankr.com/eth",
            ChainId::EthGoerli => "https://rpc.ankr.com/eth_goerli",
            ChainId::PolygonMainnet => "https://rpc.ankr.com/polygon",
            ChainId::PolygonMumbai => "https://rpc.ankr.com/polygon_mumbai",
            ChainId::FilecoinHyperspaceTestnet => {
                "https://api.hyperspace.node.glif.io/rpc/v1"
            }
        };
        Url::parse(raw_url).expect("unit test catches panics")
    }

    pub fn explorer_url(&self) -> Url {
        let raw_url = match *self {
            Self::EthMainnet => "https://etherscan.io/",
            Self::EthGoerli => "https://goerli.etherscan.io/",
            Self::PolygonMainnet => "https://polygonscan.com/",
            Self::PolygonMumbai => "https://mumbai.polygonscan.com/",
            Self::FilecoinHyperspaceTestnet => "https://hyperspace.filfox.info/en/",
        };
        Url::parse(raw_url).expect("unit test catches panics")
    }

    pub fn max_gas_price(&self) -> U256 {
        let units = match *self {
            Self::EthMainnet => parse_units("100", "gwei"),
            Self::EthGoerli => parse_units("100", "gwei"),
            Self::PolygonMainnet => parse_units("1000", "gwei"),
            Self::PolygonMumbai => parse_units("1000", "gwei"),
            Self::FilecoinHyperspaceTestnet => parse_units("1000", "gwei"),
        }
        .expect("unit test catches panics");

        match units {
            ParseUnits::U256(amount) => amount,
            // Max gas price cannot be negative. Unit test checks this exhaustively.
            ParseUnits::I256(_) => unreachable!(),
        }
    }

    fn default_dapp_allotment(&self) -> NativeTokenAmount {
        let amount = match *self {
            Self::EthMainnet => "0.1",
            Self::EthGoerli => "0.1",
            Self::PolygonMainnet => "0.1",
            Self::PolygonMumbai => "0.1",
            Self::FilecoinHyperspaceTestnet => "0.2",
        };

        NativeTokenAmount::new_from_decimal(*self, amount)
            .expect("unit test catches panics")
    }

    pub fn default_user_settings(&self) -> ChainSettings {
        let default_dapp_allotment = self.default_dapp_allotment();
        ChainSettings::new(default_dapp_allotment)
    }
}

impl From<ChainId> for u64 {
    fn from(chain_id: ChainId) -> Self {
        chain_id as u64
    }
}

impl TryFrom<u64> for ChainId {
    type Error = Error;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        FromPrimitive::from_u64(value).ok_or_else(|| Error::Retriable {
            error: format!("Unsupported u64 chain id: {}", value),
        })
    }
}

impl From<ChainId> for U64 {
    fn from(chain_id: ChainId) -> Self {
        let chain_id: u64 = chain_id.into();
        chain_id.into()
    }
}

impl TryFrom<U64> for ChainId {
    type Error = Error;

    fn try_from(value: U64) -> Result<Self, Self::Error> {
        value.as_u64().try_into()
    }
}

impl From<ChainId> for U256 {
    fn from(chain_id: ChainId) -> Self {
        let chain_id: u64 = chain_id.into();
        chain_id.into()
    }
}

impl From<ChainId> for Chain {
    fn from(value: ChainId) -> Self {
        let chain_id: u64 = value.into();
        chain_id.try_into().expect("unit test catches panics")
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use ethers::core::types::U256;
    use strum::IntoEnumIterator;

    use super::*;

    #[test]
    fn to_json() {
        let chain_id = ChainId::EthMainnet;
        let s = serde_json::to_string(&chain_id).unwrap();
        assert_eq!(s, format!("\"{}\"", chain_id));
        assert_eq!(s, r#""eth-mainnet""#);
    }

    #[test]
    fn to_string() {
        assert_eq!(ChainId::EthMainnet.to_string(), "eth-mainnet");
    }

    #[test]
    fn from_string() -> Result<()> {
        let bp = ChainId::try_from("polygon-mumbai")?;

        assert_eq!(bp, ChainId::PolygonMumbai);

        Ok(())
    }

    #[test]
    fn default_dapp_allotments_dont_panic() -> Result<()> {
        let mut count = U256::zero();
        for chain_id in ChainId::iter() {
            let amount = chain_id.default_dapp_allotment();
            count += amount.amount;
        }

        assert!(count > U256::zero());
        Ok(())
    }

    #[test]
    fn max_gas_price_no_panic() -> Result<()> {
        let mut count = U256::zero();
        for chain_id in ChainId::iter() {
            count += chain_id.max_gas_price();
        }

        assert!(count > U256::zero());
        Ok(())
    }

    #[test]
    fn to_ethers_no_panic() -> Result<()> {
        let mut count = 0u64;
        for chain_id in ChainId::iter() {
            let _chain: Chain = chain_id.into();
            count += 1;
        }

        assert!(count > 0);
        Ok(())
    }

    #[test]
    fn chain_rpc_endpoints_dont_panic() {
        for chain_id in ChainId::iter() {
            assert!(chain_id.http_rpc_endpoint().host().is_some())
        }
    }

    #[test]
    fn chain_explorer_urls_dont_panic() {
        for chain_id in ChainId::iter() {
            assert!(chain_id.explorer_url().host().is_some())
        }
    }

    #[test]
    fn network_version() {
        assert_eq!(ChainId::PolygonMainnet.network_version(), "137");
    }

    #[test]
    fn display_hex() {
        assert_eq!(ChainId::PolygonMainnet.display_hex(), "0x89");
    }
}
