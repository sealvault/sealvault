// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt;

use ethers::core::{types::Address, utils::to_checksum};
use k256::PublicKey;
use sha3::{Digest, Keccak256};

use crate::{
    protocols::{
        checksum_address::ChecksumAddress,
        eth::{chain_id::ChainId, EthereumAsymmetricKey, ProtocolData},
    },
    Error,
};

#[readonly::make]
pub struct SigningKey {
    pub chain_id: ChainId,
    pub key: EthereumAsymmetricKey,
    pub address: Address,
}

impl SigningKey {
    pub fn new(key: EthereumAsymmetricKey, chain_id: ChainId) -> Result<Self, Error> {
        let address = public_key_to_address(&key.public_key)?;
        Ok(Self {
            key,
            chain_id,
            address,
        })
    }

    pub fn protocol_data(&self) -> ProtocolData {
        ProtocolData::new(self.chain_id)
    }
}

impl ChecksumAddress for SigningKey {
    fn checksum_address(&self) -> String {
        checksum_address(&self.address)
    }
}

// https://en.bitcoin.it/wiki/BIP_0137
const UNCOMPRESSED_PUBLIC_KEY_PREFIX: u8 = 0x04;

fn public_key_to_address(public_key: &PublicKey) -> Result<Address, Error> {
    use k256::elliptic_curve::sec1::ToEncodedPoint;
    use sha3::digest::FixedOutput;

    let pk = public_key.to_encoded_point(/* compress = */ false);
    let pk = pk.as_bytes();
    if pk[0] != UNCOMPRESSED_PUBLIC_KEY_PREFIX {
        return Err(Error::Fatal {
            error: "Expected uncompressed public key".into(),
        });
    }
    let digest = Keccak256::new_with_prefix(&pk[1..]);
    let hash = digest.finalize_fixed();
    Ok(Address::from_slice(&hash[12..]))
}

pub(super) fn checksum_address(address: &Address) -> String {
    // EIP-1191 is not backward compatible with EIP-155 and it is not supported widely enough so
    // adding chain id to checksum is likely to cause more trouble than help.
    to_checksum(address, None)
}

/// Convert a Secp256k1 public key to an EIP-155 checksum address.
pub fn public_key_to_checksum_address(public_key: &PublicKey) -> Result<String, Error> {
    let address = public_key_to_address(public_key)?;
    Ok(checksum_address(&address))
}

impl fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EthereumAddress")
            .field("chain", &self.chain_id.to_string())
            .field("address", &self.address)
            .finish()
    }
}
#[cfg(test)]
mod tests {
    use anyhow::Result;
    use k256::SecretKey;

    use super::*;

    // Test vector from https://github.com/ethereumbook/ethereumbook/blob/develop/04keys-addresses.asciidoc
    #[test]
    fn correct_pk_address_conversion() -> Result<()> {
        const SK: &str =
            "f8f8a2f43c8376ccb0871305060d7b27b0554d2cc72bccf41b2705608452f315";
        const ADDRESS: &str = "001d3f1ef827552ae1114027bd3ecf1f086ba0f9";

        let sk = SecretKey::from_be_bytes(&hex::decode(SK)?)?;
        let pk = sk.public_key();

        let expected_address = Address::from_slice(&hex::decode(ADDRESS)?);
        let address = public_key_to_address(&pk)?;

        assert_eq!(address, expected_address);

        Ok(())
    }
}
