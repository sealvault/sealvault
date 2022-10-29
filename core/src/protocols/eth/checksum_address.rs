// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use ethers::core::{types::Address, utils::to_checksum};

use crate::Error;

pub fn validate_checksum_address(check_sum_address: &str) -> Result<(), Error> {
    parse_checksum_address(check_sum_address)?;
    Ok(())
}

pub fn parse_checksum_address(check_sum_address: &str) -> Result<Address, Error> {
    let addr: Address = check_sum_address.parse().map_err(|_| Error::User {
        explanation: "This doesn't look like an Ethereum checksum address.".into(),
    })?;

    if to_checksum(&addr, None) != check_sum_address {
        Err(Error::User {
            explanation: "A checksum address is required here.".into(),
        })
    } else {
        Ok(addr)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;

    #[test]
    fn checksum_address_is_ok() -> Result<()> {
        let addr = "0x8b6B4C4BaEA2fE3615adB7fB9Ae2af2b67b0077a";
        validate_checksum_address(addr)?;
        Ok(())
    }

    #[test]
    fn invalid_checksum_is_not_ok() -> Result<()> {
        // Last char is changed from valid.
        let addr = "0x8b6B4C4BaEA2fE3615adB7fB9Ae2af2b67b0077b";
        let result = validate_checksum_address(addr);
        assert!(matches!(result, Err(Error::User { explanation: _ })));
        Ok(())
    }

    #[test]
    fn no_prefix_is_not_ok() -> Result<()> {
        let addr = "8b6B4C4BaEA2fE3615adB7fB9Ae2af2b67b0077a";
        let result = validate_checksum_address(addr);
        assert!(matches!(result, Err(Error::User { explanation: _ })));
        Ok(())
    }

    #[test]
    fn lowercase_is_not_ok_for_checksum() -> Result<()> {
        let addr = "0x8b6b4c4baea2fe3615adb7fb9ae2af2b67b0077a";
        let result = validate_checksum_address(addr);
        assert!(matches!(result, Err(Error::User { explanation: _ })));
        Ok(())
    }
}
