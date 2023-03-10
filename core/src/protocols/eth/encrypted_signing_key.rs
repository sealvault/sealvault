// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
use std::fmt;

use typed_builder::TypedBuilder;

use crate::{
    encryption::{
        DataEncryptionKey, EncryptionOutput, KeyEncryptionKey, KeyName, Keychain,
    },
    protocols::eth::{chain_id::ChainId, ChecksumAddress, EthereumAsymmetricKey},
    Error,
};

#[derive(TypedBuilder)]
#[readonly::make]
pub struct EncryptedSigningKey {
    pub chain_id: ChainId,
    pub address: ChecksumAddress,
    pub encrypted_secret_key: EncryptionOutput,
    pub encrypted_dek: EncryptionOutput,
    pub dek_name: KeyName,
}

impl EncryptedSigningKey {
    /// Decrypt this encrypted secret key into a signing key.
    pub fn decrypt(&self, keychain: &Keychain) -> Result<EthereumAsymmetricKey, Error> {
        let sk_kek = KeyEncryptionKey::sk_kek(keychain)?;
        let sk_dek = DataEncryptionKey::from_encrypted(
            self.dek_name,
            &self.encrypted_dek,
            &sk_kek,
        )?;
        EthereumAsymmetricKey::from_encrypted_der(&self.encrypted_secret_key, &sk_dek)
    }
}

impl fmt::Debug for EncryptedSigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EthereumAddress")
            .field("chain", &self.chain_id.to_string())
            .field("address", &self.address)
            .field("dek_name", &self.dek_name.to_string())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl EncryptedSigningKey {
        pub fn random_test_key(
            keychain: &Keychain,
            chain_id: ChainId,
        ) -> Result<Self, Error> {
            let secret_key = EthereumAsymmetricKey::random()?;

            Self::test_key(keychain, secret_key, chain_id)
        }

        pub fn test_key(
            keychain: &Keychain,
            secret_key: EthereumAsymmetricKey,
            chain_id: ChainId,
        ) -> Result<Self, Error> {
            let sk_kek = KeyEncryptionKey::sk_kek(keychain).or_else(|_| {
                let sk_kek = KeyEncryptionKey::random(KeyName::SkKeyEncryptionKey)?;
                sk_kek.upsert_to_local_keychain(keychain)?;
                KeyEncryptionKey::sk_kek(keychain)
            })?;

            let dek_name = KeyName::SkDataEncryptionKey;
            let sk_dek = DataEncryptionKey::random(dek_name)?;
            let encrypted_dek = sk_dek.to_encrypted(&sk_kek)?;

            let encrypted_secret_key = secret_key.to_encrypted_der(&sk_dek)?;

            let address = ChecksumAddress::new(&secret_key.public_key)?;

            Ok(Self {
                chain_id,
                address,
                encrypted_secret_key,
                encrypted_dek,
                dek_name,
            })
        }
    }
}
