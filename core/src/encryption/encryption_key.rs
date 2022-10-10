// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter};

use zeroize::Zeroizing;

use crate::{
    encryption::{
        encrypt_decrypt::{decrypt, encrypt},
        encryption_output::EncryptionOutput,
        key_material::KeyMaterial,
    },
    Error,
};

/// We need separate data encryption and key encryption key types to prevent encrypting data by
/// accident with a key encryption.
/// Some repetition could be saved with a proc macro, but not enough to warrant a separate crate for
/// it.

// Only exposed in the encryption module to simplify following data-flows.
pub(super) trait ExposeKeyMaterial<'a> {
    fn expose_key_material(&'a self) -> &'a KeyMaterial;
}

/// Data encryption key.
#[derive(Debug)]
#[readonly::make]
pub struct DataEncryptionKey(SymmetricKey);

impl DataEncryptionKey {
    pub fn name(&self) -> &str {
        &self.0.name
    }

    pub fn random(name: String) -> Result<Self, Error> {
        Ok(Self(SymmetricKey::new(name, KeyMaterial::random()?)))
    }

    pub fn from_encrypted(
        name: String,
        encryption_output: &EncryptionOutput,
        encryption_key: &KeyEncryptionKey,
    ) -> Result<Self, Error> {
        let payload = aead::Payload {
            msg: &encryption_output.cipher_text,
            aad: name.as_bytes(),
        };
        // The vector returned by decrypt is allocated with the desired capacity by the underlying
        // library, so leaving copies of key material in memory on vector reallocation that won't be
        // zeroized on drop is not a concern.
        let key_bytes =
            Zeroizing::new(decrypt(payload, encryption_key, &encryption_output.nonce)?);
        let encryption_key = KeyMaterial::from_slice(key_bytes.as_slice())?;

        Ok(Self(SymmetricKey::new(name, encryption_key)))
    }

    pub fn to_encrypted(
        &self,
        with_key: &KeyEncryptionKey,
    ) -> Result<EncryptionOutput, Error> {
        let payload = aead::Payload {
            msg: self.expose_key_material().as_ref(),
            aad: self.name().as_bytes(),
        };
        encrypt(payload, with_key)
    }

    pub fn encrypt_secret(
        &self,
        secret: &Zeroizing<Vec<u8>>,
    ) -> Result<EncryptionOutput, Error> {
        encrypt(secret.as_slice(), self)
    }

    pub fn decrypt_secret(
        &self,
        encrypted_secret: &EncryptionOutput,
    ) -> Result<Zeroizing<Vec<u8>>, Error> {
        Ok(Zeroizing::new(decrypt(
            encrypted_secret.cipher_text.as_slice(),
            self,
            &encrypted_secret.nonce,
        )?))
    }
}

impl<'a> ExposeKeyMaterial<'a> for DataEncryptionKey {
    fn expose_key_material(&'a self) -> &'a KeyMaterial {
        &self.0.key_material
    }
}

/// Encryption key for data encryption keys.
#[derive(Debug)]
#[readonly::make]
pub struct KeyEncryptionKey(SymmetricKey);

impl KeyEncryptionKey {
    pub(super) fn new(name: String, encryption_key: KeyMaterial) -> Self {
        Self(SymmetricKey::new(name, encryption_key))
    }

    pub fn name(&self) -> &str {
        &self.0.name
    }

    pub fn random(name: String) -> Result<Self, Error> {
        Ok(Self::new(name, KeyMaterial::random()?))
    }

    /// Decompose the struct into name and key material.
    pub(super) fn into_keychain(self) -> (String, KeyMaterial) {
        let SymmetricKey { name, key_material } = self.0;
        (name, key_material)
    }
}

impl<'a> ExposeKeyMaterial<'a> for KeyEncryptionKey {
    fn expose_key_material(&'a self) -> &'a KeyMaterial {
        &self.0.key_material
    }
}

/// Wrapper for a 256-bit symmetric encryption key.
#[readonly::make]
struct SymmetricKey {
    pub name: String,
    pub(super) key_material: KeyMaterial,
}

impl SymmetricKey {
    pub(super) fn new(name: String, key_material: KeyMaterial) -> Self {
        Self { name, key_material }
    }
}

impl Debug for SymmetricKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymmetricKey")
            .field("name", &self.name)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;

    #[test]
    fn encrypt_decrypt_dek() -> Result<()> {
        let dek_name = "dek";
        let dek = DataEncryptionKey::random(dek_name.into())?;
        let kek = KeyEncryptionKey::random("kek".into())?;
        let encryption_output = dek.to_encrypted(&kek)?;
        let decrypted_key =
            DataEncryptionKey::from_encrypted(dek_name.into(), &encryption_output, &kek)?;

        assert_eq!(dek.name(), decrypted_key.name());

        Ok(())
    }

    #[test]
    fn checks_name_on_dek_decryption() -> Result<()> {
        let dek = DataEncryptionKey::random("dek".into())?;
        let kek = KeyEncryptionKey::random("kek".into())?;
        let encryption_output = dek.to_encrypted(&kek)?;
        let result =
            DataEncryptionKey::from_encrypted("not-dek".into(), &encryption_output, &kek);
        assert!(matches!(result,
                Err(Error::Fatal {
                    error
                }) if error.to_lowercase().to_lowercase().contains("aead")));
        Ok(())
    }
}
