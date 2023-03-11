// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    fmt::{Display, Formatter},
    hash::{Hash, Hasher},
    str::FromStr,
};

use core_macros::sql_text;
use derive_more::{AsRef, From, Into};
use diesel::expression::AsExpression;
use ethers::core::{types::Address, utils::to_checksum};
use k256::PublicKey;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Keccak256};

use crate::{CoreError, Error};

// https://en.bitcoin.it/wiki/BIP_0137
const UNCOMPRESSED_PUBLIC_KEY_PREFIX: u8 = 0x04;

#[derive(
    Debug,
    Clone,
    Copy,
    Into,
    From,
    AsRef,
    AsExpression,
    FromSqlRow,
    Serialize,
    Deserialize,
)]
#[serde(try_from = "String")]
#[serde(into = "String")]
#[diesel(sql_type = diesel::sql_types::Text)]
#[as_ref(forward)]
#[repr(transparent)]
pub struct ChecksumAddress(Address);

impl ChecksumAddress {
    pub fn new(public_key: &PublicKey) -> Result<Self, Error> {
        use k256::elliptic_curve::sec1::ToEncodedPoint;
        use sha3::digest::FixedOutput;

        let pk = public_key.to_encoded_point(/* compress = */ false);
        let pk = pk.as_bytes();
        if pk[0] != UNCOMPRESSED_PUBLIC_KEY_PREFIX {
            return Err(Error::Fatal {
                error: "Expected uncompressed public key.".into(),
            });
        }
        let digest = Keccak256::new_with_prefix(&pk[1..]);
        let hash = digest.finalize_fixed();

        Ok(Self(Address::from_slice(&hash[12..])))
    }

    pub fn to_address(self) -> Address {
        self.0
    }
}

impl TryFrom<String> for ChecksumAddress {
    type Error = ChecksumAddressError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.parse()
    }
}

impl FromStr for ChecksumAddress {
    type Err = ChecksumAddressError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let address: Address = value
            .parse()
            .map_err(|_| ChecksumAddressError::NotAnAddress)?;
        let checksum = Self(address);

        if checksum.to_string() != value {
            Err(ChecksumAddressError::InvalidChecksum)
        } else {
            Ok(checksum)
        }
    }
}

impl From<ChecksumAddress> for String {
    fn from(value: ChecksumAddress) -> Self {
        value.to_string()
    }
}

impl PartialEq<Address> for ChecksumAddress {
    fn eq(&self, other: &Address) -> bool {
        self.0.eq(other)
    }
}

impl PartialEq<Self> for ChecksumAddress {
    fn eq(&self, other: &Self) -> bool {
        self.eq(&other.0)
    }
}

impl Eq for ChecksumAddress {}

impl Hash for ChecksumAddress {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Address::hash(&self.0, state)
    }
}

impl Display for ChecksumAddress {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // EIP-1191 is not backward compatible with EIP-155 and it is not supported widely enough so
        // adding chain id to checksum is likely to cause more trouble than help.
        write!(f, "{}", to_checksum(&self.0, None))
    }
}

sql_text!(ChecksumAddress);

#[derive(Debug, thiserror::Error)]
pub enum ChecksumAddressError {
    #[error("The provided value is not an Ethereum address.")]
    NotAnAddress,
    #[error("Invalid checksum for address.")]
    InvalidChecksum,
}

impl From<ChecksumAddressError> for CoreError {
    fn from(value: ChecksumAddressError) -> Self {
        match value {
            ChecksumAddressError::NotAnAddress => CoreError::User {
                explanation: "This doesn't look like an Ethereum checksum address."
                    .into(),
            },
            ChecksumAddressError::InvalidChecksum => CoreError::User {
                explanation: "A checksum address is required here.".into(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use ethers::core::k256::FieldBytes;
    use k256::SecretKey;

    use super::*;

    #[test]
    fn checksum_address_is_ok() -> Result<()> {
        let s = "0x8b6B4C4BaEA2fE3615adB7fB9Ae2af2b67b0077a";
        let address: ChecksumAddress = s.parse()?;
        assert_eq!(address.to_string(), s);
        Ok(())
    }

    #[test]
    fn invalid_checksum_is_not_ok() -> Result<()> {
        // Last char is changed from valid.
        let result: Result<ChecksumAddress, ChecksumAddressError> =
            "0x8b6B4C4BaEA2fE3615adB7fB9Ae2af2b67b0077b".parse();
        assert!(matches!(result, Err(_)));
        Ok(())
    }

    #[test]
    fn no_prefix_is_not_ok() -> Result<()> {
        let result: Result<ChecksumAddress, ChecksumAddressError> =
            "8b6B4C4BaEA2fE3615adB7fB9Ae2af2b67b0077a".parse();
        dbg!(&result);
        assert!(matches!(result, Err(_)));
        Ok(())
    }

    #[test]
    fn lowercase_is_not_ok_for_checksum() -> Result<()> {
        let result: Result<ChecksumAddress, ChecksumAddressError> =
            "0x8b6b4c4baea2fe3615adb7fb9ae2af2b67b0077a".parse();
        assert!(matches!(result, Err(_)));
        Ok(())
    }

    // Test vector from https://github.com/ethereumbook/ethereumbook/blob/develop/04keys-addresses.asciidoc
    #[test]
    fn correct_pk_address_conversion() -> Result<()> {
        const SK: &str =
            "f8f8a2f43c8376ccb0871305060d7b27b0554d2cc72bccf41b2705608452f315";
        const ADDRESS: &str = "001d3f1ef827552ae1114027bd3ecf1f086ba0f9";

        let sk = hex::decode(SK)?;
        let field_bytes = FieldBytes::from_slice(&sk);
        let sk = SecretKey::from_bytes(&field_bytes)?;
        let pk = sk.public_key();

        let expected_address = Address::from_slice(&hex::decode(ADDRESS)?);
        let address = ChecksumAddress::new(&pk)?;

        assert_eq!(&address, &expected_address);

        Ok(())
    }
}
