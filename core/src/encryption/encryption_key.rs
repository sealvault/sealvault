// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter};

use aead::Payload;
use generic_array::typenum::U32;
use zeroize::Zeroizing;

use crate::{
    backup::BackupMetadata,
    encryption::{
        encrypt_decrypt::{decrypt, encrypt},
        encryption_output::EncryptionOutput,
        key_material::KeyMaterial,
        KeyName, Keychain,
    },
    Error,
};

// We need separate data encryption and key encryption key types to prevent encrypting data by
// accident with a key encryption.
// Some repetition could be saved with a proc macro, but not enough to warrant a separate crate for
// it.

type EncryptionKey = KeyMaterial<U32>;

// Only exposed in the encryption module to simplify following data-flows.
pub(super) trait ExposeKeyMaterial<'a> {
    fn expose_secret(&'a self) -> &'a EncryptionKey;
}

/// Data encryption key.
#[derive(Debug)]
#[readonly::make]
pub struct DataEncryptionKey(SymmetricKey);

impl DataEncryptionKey {
    pub(super) fn new(name: KeyName, encryption_key: EncryptionKey) -> Self {
        Self(SymmetricKey::new(name, encryption_key))
    }

    pub fn db_backup_dek(keychain: &Keychain) -> Result<Self, Error> {
        let name = KeyName::DbBackupDataEncryptionKey;
        let key: EncryptionKey = keychain.get_local(name)?;
        Ok(Self::new(name, key))
    }

    pub fn from_encrypted(
        name: KeyName,
        encrypted_dek: &EncryptionOutput,
        encryption_key: &KeyEncryptionKey,
    ) -> Result<Self, Error> {
        let name_str: &str = name.as_ref();
        let payload = Payload {
            msg: &encrypted_dek.cipher_text,
            aad: name_str.as_bytes(),
        };
        // The vector returned by decrypt is allocated with the desired capacity by the underlying
        // library, so leaving copies of key material in memory on vector reallocation that won't be
        // zeroized on drop is not a concern.
        let key_bytes =
            Zeroizing::new(decrypt(payload, encryption_key, &encrypted_dek.nonce)?);
        let encryption_key = KeyMaterial::from_slice(key_bytes.as_slice())?;

        Ok(Self(SymmetricKey::new(name, encryption_key)))
    }

    pub fn name(&self) -> &str {
        self.0.name.as_ref()
    }

    pub fn random(name: KeyName) -> Result<Self, Error> {
        Ok(Self(SymmetricKey::new(name, KeyMaterial::random()?)))
    }

    pub fn to_encrypted(
        &self,
        with_key: &KeyEncryptionKey,
    ) -> Result<EncryptionOutput, Error> {
        let payload = Payload {
            msg: self.expose_secret().as_ref(),
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

    /// Encrypt a file at a given path and write it to the out path. Assumes the file fits into
    /// memory. It'd be preferable to use streaming encryption and not read the entire file into
    /// memory but streaming AEAD is immature in Rust and naive implementations are dangerous.
    pub fn encrypt_backup(
        &self,
        backup_contents: &[u8],
        metadata: &BackupMetadata,
    ) -> Result<EncryptionOutput, Error> {
        let meta_ser = metadata.canonical_json()?;

        let payload = Payload {
            msg: backup_contents,
            aad: meta_ser.as_ref(),
        };

        encrypt(payload, self)
    }

    pub fn decrypt_backup(
        &self,
        encryption_output: &EncryptionOutput,
        metadata: &BackupMetadata,
    ) -> Result<Vec<u8>, Error> {
        let meta_ser = metadata.canonical_json()?;

        let payload = Payload {
            msg: &encryption_output.cipher_text,
            aad: meta_ser.as_ref(),
        };

        decrypt(payload, self, &encryption_output.nonce)
    }

    pub fn upsert_to_local_keychain(self, keychain: &Keychain) -> Result<(), Error> {
        upsert_to_local_keychain(keychain, self.0)
    }

    pub fn delete_from_keychain_if_exists(
        keychain: &Keychain,
        name: KeyName,
    ) -> Result<(), Error> {
        keychain.delete_local_if_exists(name)?;
        Ok(())
    }
}

impl<'a> ExposeKeyMaterial<'a> for DataEncryptionKey {
    fn expose_secret(&'a self) -> &'a EncryptionKey {
        &self.0.key_material
    }
}

/// Encryption key for data encryption keys.
#[derive(Debug)]
#[readonly::make]
pub struct KeyEncryptionKey(SymmetricKey);

impl KeyEncryptionKey {
    pub(super) fn new(name: KeyName, encryption_key: EncryptionKey) -> Self {
        Self(SymmetricKey::new(name, encryption_key))
    }

    pub fn sk_kek(keychain: &Keychain) -> Result<Self, Error> {
        Self::from_keychain(keychain, KeyName::SkKeyEncryptionKey)
    }

    pub fn sk_backup_kek(keychain: &Keychain) -> Result<Self, Error> {
        Self::from_keychain(keychain, KeyName::SkBackupKeyEncryptionKey)
    }

    fn from_keychain(keychain: &Keychain, name: KeyName) -> Result<Self, Error> {
        let key: EncryptionKey = keychain.get_local(name)?;
        Ok(Self::new(name, key))
    }

    pub fn name(&self) -> &str {
        self.0.name.as_ref()
    }

    pub fn random(name: KeyName) -> Result<Self, Error> {
        Ok(Self::new(name, KeyMaterial::random()?))
    }

    pub fn upsert_to_local_keychain(self, keychain: &Keychain) -> Result<(), Error> {
        upsert_to_local_keychain(keychain, self.0)
    }

    pub fn delete_from_keychain_if_exists(
        keychain: &Keychain,
        name: KeyName,
    ) -> Result<(), Error> {
        keychain.delete_local_if_exists(name)?;
        Ok(())
    }
}

impl<'a> ExposeKeyMaterial<'a> for KeyEncryptionKey {
    fn expose_secret(&'a self) -> &'a EncryptionKey {
        &self.0.key_material
    }
}

/// Wrapper for a 256-bit symmetric encryption key.
#[readonly::make]
struct SymmetricKey {
    pub name: KeyName,
    pub(super) key_material: EncryptionKey,
}

impl SymmetricKey {
    pub(super) fn new(name: KeyName, key_material: EncryptionKey) -> Self {
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

fn upsert_to_local_keychain(keychain: &Keychain, key: SymmetricKey) -> Result<(), Error> {
    let SymmetricKey { name, key_material } = key;
    keychain.upsert_local(name, key_material)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;

    #[test]
    fn encrypt_decrypt_dek() -> Result<()> {
        let dek = DataEncryptionKey::random(KeyName::SkDataEncryptionKey)?;
        let kek = KeyEncryptionKey::random(KeyName::SkKeyEncryptionKey)?;
        let encryption_output = dek.to_encrypted(&kek)?;
        let decrypted_key = DataEncryptionKey::from_encrypted(
            KeyName::SkDataEncryptionKey,
            &encryption_output,
            &kek,
        )?;

        assert_eq!(dek.name(), decrypted_key.name());

        Ok(())
    }

    #[test]
    fn checks_name_on_dek_decryption() -> Result<()> {
        let dek = DataEncryptionKey::random(KeyName::SkDataEncryptionKey)?;
        let kek = KeyEncryptionKey::random(KeyName::SkKeyEncryptionKey)?;
        let encryption_output = dek.to_encrypted(&kek)?;
        let result = DataEncryptionKey::from_encrypted(
            KeyName::SkKeyEncryptionKey,
            &encryption_output,
            &kek,
        );
        assert!(matches!(result,
                Err(Error::Fatal {
                    error
                }) if error.to_lowercase().to_lowercase().contains("aead")));
        Ok(())
    }
}
