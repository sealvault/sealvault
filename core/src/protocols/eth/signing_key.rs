// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt;

use crate::{
    protocols::eth::{
        chain_id::ChainId, ChecksumAddress, EthereumAsymmetricKey, ProtocolData,
    },
    Error,
};

#[readonly::make]
pub struct SigningKey {
    pub chain_id: ChainId,
    pub key: EthereumAsymmetricKey,
    pub address: ChecksumAddress,
}

impl SigningKey {
    pub fn new(key: EthereumAsymmetricKey, chain_id: ChainId) -> Result<Self, Error> {
        let address = ChecksumAddress::new(&key.public_key)?;
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

impl fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EthereumAddress")
            .field("chain", &self.chain_id.to_string())
            .field("address", &self.address)
            .finish()
    }
}
