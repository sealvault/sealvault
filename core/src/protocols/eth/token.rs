// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
use ethers::{
    core::types::{Address, U256},
    utils::to_checksum,
};
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use strum_macros::{Display, EnumIter, EnumString};

use crate::{assets::load_binary, config, protocols::eth::ChainId, Error};

#[derive(Debug, PartialEq, EnumIter, EnumString, Display, Serialize, Deserialize)]
#[strum(serialize_all = "UPPERCASE")]
#[serde(rename_all = "UPPERCASE")]
pub enum NativeToken {
    Eth,
    Matic,
}

impl NativeToken {
    /// The smallest transferable fraction of the native token is `10^{-decimals}`
    pub fn decimals(&self) -> u8 {
        match *self {
            Self::Eth => 18,
            Self::Matic => 18,
        }
    }

    pub fn icon(&self) -> Result<Vec<u8>, Error> {
        let icon_path = format!(
            "{}/{}{}",
            config::ETH_NATIVE_TOKEN_PREFIX,
            &self,
            config::NATIVE_TOKEN_EXTENSION
        );
        load_binary(&icon_path)
    }

    pub fn symbol(&self) -> String {
        self.to_string()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[readonly::make]
pub struct NativeTokenAmount {
    pub chain_id: ChainId,
    /// Amount of native tokens in the lowest denomination of the chain (eg. Wei on Ethereum).
    pub amount: U256,
}

impl NativeTokenAmount {
    pub fn new(chain_id: ChainId, amount: U256) -> Self {
        Self { chain_id, amount }
    }

    pub fn new_from_decimal(
        chain_id: ChainId,
        amount_decimal: &str,
    ) -> Result<Self, Error> {
        let amount = parse_amount(amount_decimal, chain_id.native_token().decimals())?;
        Ok(Self { chain_id, amount })
    }

    /// Native token amount denominated in the highest denomination of the chain
    /// in decimal. Eg. "1" is Ether on Ethereum and "0.000000001" is 1 Gwei on Ethereum.
    pub fn display_amount(&self) -> String {
        display_amount(self.amount, self.chain_id.native_token().decimals())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[readonly::make]
pub struct FungibleToken {
    pub chain_id: ChainId,
    pub contract_address: Address,
    pub decimals: u8,
}

impl FungibleToken {
    pub fn new(chain_id: ChainId, contract_address: Address, decimals: u8) -> Self {
        Self {
            chain_id,
            contract_address,
            decimals,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[readonly::make]
pub struct FungibleTokenAmount {
    pub token: FungibleToken,
    /// Amount of fungible tokens in the lowest denomination.
    pub amount: U256,
}

impl FungibleTokenAmount {
    pub fn new(token: FungibleToken, amount: U256) -> Self {
        Self { token, amount }
    }

    pub fn new_from_decimal(
        token: FungibleToken,
        amount_decimal: &str,
    ) -> Result<Self, Error> {
        let amount = parse_amount(amount_decimal, token.decimals)?;
        Ok(Self { token, amount })
    }

    /// Native token amount denominated in the highest denomination of the token
    /// in decimal.
    pub fn display_amount(&self) -> String {
        display_amount(self.amount, self.token.decimals)
    }
}

/// Based on
/// https://github.com/gakonst/ethers-rs/blob/3681099af328610b429fd22eab5e9f68f693c60c/ethers-core/src/utils/mod.rs#L101
fn display_amount(amount: U256, decimals: u8) -> String {
    let decimals_us: usize = decimals.into();
    let scale = U256::exp10(decimals_us);

    let amount_decimals = amount % scale;
    let amount_integer = amount / scale;

    let mut res = format!(
        "{}.{:0width$}",
        amount_integer,
        amount_decimals,
        width = decimals_us
    );
    // Remove trailing zeroes
    while res.ends_with('0') {
        res.pop();
    }
    if res.ends_with('.') {
        res.pop();
    }
    res
}

fn parse_amount(amount: &str, decimals: u8) -> Result<U256, Error> {
    use rust_decimal::MathematicalOps;

    // Some locales use "," as the decimal separator instead of ".", hence the replace.
    let num: Decimal =
        amount
            .replace(',', ".")
            .parse()
            .map_err(|_| Error::Retriable {
                error: format!("Invalid decimal string: '{}'", amount),
            })?;

    let multiplier: Decimal =
        Decimal::TEN
            .checked_powu(decimals.into())
            .ok_or_else(|| Error::Fatal {
                error: format!("Too many decimals: {}", decimals),
            })?;
    let val = num
        .checked_mul(multiplier)
        .ok_or_else(|| Error::Retriable {
            error: format!(
                "Parsing amount {} with decimals {} overflowed",
                amount, decimals
            ),
        })?;
    U256::from_dec_str(&val.round().to_string()).map_err(|_| Error::Retriable {
        error: format!("Cannot parse {} as U256", val),
    })
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FungibleTokenBalance {
    pub chain_id: ChainId,
    pub contract_address: Address,
    pub amount: U256,
    pub decimals: u8,
    pub symbol: String,
    pub name: String,
    pub logo: Option<url::Url>,
}

impl FungibleTokenBalance {
    pub fn display_amount(&self) -> String {
        display_amount(self.amount, self.decimals)
    }

    pub fn display_contract_address(&self) -> String {
        to_checksum(&self.contract_address, None)
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Mul;

    use anyhow::Result;
    use strum::IntoEnumIterator;

    use super::*;

    #[test]
    fn parse_amount_fractional() -> Result<()> {
        // This should be covered by prop testing, but after reviewing the options, Quickcheck is
        // poorly documented and difficult to work with, and Proptest is unmaintained.
        // We should periodically reevaluate property-based testing options though.

        assert!(parse_amount("", 2).is_err());
        assert!(parse_amount(".", 2).is_err());
        assert!(parse_amount(",", 2).is_err());

        assert_eq!(parse_amount("12.", 0)?, U256::from_dec_str("12")?);
        assert_eq!(parse_amount("12,", 0)?, U256::from_dec_str("12")?);
        assert_eq!(parse_amount(".12", 2)?, U256::from_dec_str("12")?);
        assert_eq!(parse_amount(",12", 2)?, U256::from_dec_str("12")?);
        assert_eq!(parse_amount("0.12", 2)?, U256::from_dec_str("12")?);
        assert_eq!(parse_amount("0,12", 2)?, U256::from_dec_str("12")?);
        assert_eq!(parse_amount("123.45", 2)?, U256::from_dec_str("12345")?);
        assert_eq!(parse_amount("123,45", 2)?, U256::from_dec_str("12345")?);

        assert!(parse_amount("12.34,56", 2).is_err());
        assert!(parse_amount("12,34.56", 2).is_err());

        Ok(())
    }

    #[test]
    fn new_amount_from_decimal_str() -> Result<()> {
        fn expected_amount(amount: u64, decimals: u8) -> U256 {
            let n = U256::exp10(decimals as usize);
            U256::from(amount).mul(n)
        }

        for chain_id in ChainId::iter() {
            let decimals = chain_id.native_token().decimals();
            let amount = NativeTokenAmount::new_from_decimal(ChainId::EthMainnet, "0")?;
            assert_eq!(amount.amount, U256::zero());
            let amount =
                NativeTokenAmount::new_from_decimal(ChainId::EthMainnet, "0.3333")?;
            assert_eq!(amount.amount, expected_amount(3333, decimals - 4));
            let amount = NativeTokenAmount::new_from_decimal(ChainId::EthMainnet, "1")?;
            assert_eq!(amount.amount, expected_amount(1, 18));
            let amount =
                NativeTokenAmount::new_from_decimal(ChainId::EthMainnet, "1.39563324")?;
            assert_eq!(amount.amount, expected_amount(139563324, decimals - 8));
            let amount =
                NativeTokenAmount::new_from_decimal(ChainId::EthMainnet, "1234")?;
            assert_eq!(amount.amount, expected_amount(1234, decimals));
            let amount =
                NativeTokenAmount::new_from_decimal(ChainId::EthMainnet, "1234.56")?;
            assert_eq!(amount.amount, expected_amount(123456, decimals - 2));
        }
        Ok(())
    }

    #[test]
    fn native_to_string() {
        assert_eq!(NativeToken::Eth.to_string(), "ETH");
        assert_eq!(NativeToken::Eth.symbol(), "ETH");
    }

    #[test]
    fn native_from_string() -> Result<()> {
        let nt = NativeToken::try_from("MATIC")?;

        assert_eq!(nt, NativeToken::Matic);

        Ok(())
    }

    #[test]
    fn all_have_icons() -> Result<()> {
        for token in NativeToken::iter() {
            let icon = token.icon()?;
            assert!(!icon.is_empty())
        }
        Ok(())
    }

    #[test]
    fn test_display_amount() {
        let decimals: u8 = 18;

        // Based on
        // https://github.com/gakonst/ethers-rs/blob/3681099af328610b429fd22eab5e9f68f693c60c/ethers-core/src/utils/mod.rs#L427
        let eth = display_amount(1395633240123456000_u128.into(), decimals);
        assert_eq!(eth.parse::<f64>().unwrap(), 1.395633240123456);

        let amount = U256::from_dec_str("1395633240123456000").unwrap();
        let eth = display_amount(amount, decimals);
        assert_eq!(eth.parse::<f64>().unwrap(), 1.395633240123456);

        let amount = U256::from_dec_str("1395633240123456789").unwrap();
        assert_eq!(display_amount(amount, decimals), "1.395633240123456789");

        let amount = U256::from_dec_str("1005633240123456789").unwrap();
        assert_eq!(display_amount(amount, decimals), "1.005633240123456789");

        let amount = U256::exp10(18);
        assert_eq!(display_amount(amount, decimals), "1");

        let amount = U256::zero();
        assert_eq!(display_amount(amount, decimals), "0");

        let amount = U256::exp10(19) + U256::exp10(16);
        assert_eq!(display_amount(amount, decimals), "10.01");

        let amount = U256::exp10(9);
        assert_eq!(display_amount(amount, decimals), "0.000000001");

        let amount = U256::exp10(3);
        assert_eq!(display_amount(amount, 0), "1000");
    }

    #[test]
    fn test_display_native_token_amount() {
        let nta = NativeTokenAmount::new(ChainId::EthMainnet, U256::exp10(18));
        assert_eq!(nta.display_amount(), "1")
    }
}
