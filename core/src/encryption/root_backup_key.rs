// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use argon2::{Algorithm, Argon2, ParamsBuilder, Version};
use generic_array::{typenum::U32, GenericArray};
use zeroize::Zeroizing;

use crate::{
    encryption::{
        kdf_secret::KdfSecret, key_material::KeyMaterial, BackupPassword,
        DataEncryptionKey, KdfNonce, KeyEncryptionKey, KeyName,
    },
    Error,
};

// Argon is very slow in debug builds.
#[cfg(not(test))]
const MEMORY_COST_KIB: u32 = 64 * 1024;
#[cfg(test)]
const MEMORY_COST_KIB: u32 = 8;

#[cfg(not(test))]
const ITERATIONS: u32 = 10;
#[cfg(test)]
const ITERATIONS: u32 = 1;

const PARALLELISM: u32 = 1;
const TAG_BYTES: usize = 32;

const MIN_BLAKE_CONTEXT_LEN: usize = 100;

/// The root cloud backup key that is derived from the backup password.
/// More: https://sealvault.org/dev-docs/design/backup/#key-derivation-functions
pub struct RootBackupKey(KeyMaterial<U32>);

impl RootBackupKey {
    pub fn derive_from(
        backup_password: &BackupPassword,
        kdf_secret: &KdfSecret,
        kdf_nonce: &KdfNonce,
    ) -> Result<Self, Error> {
        let mut builder = ParamsBuilder::new();
        builder
            .m_cost(MEMORY_COST_KIB)
            .t_cost(ITERATIONS)
            .p_cost(PARALLELISM)
            .output_len(TAG_BYTES);
        let params = builder.build()?;

        let argon = Argon2::new_with_secret(
            kdf_secret.expose_secret(),
            Algorithm::Argon2id,
            Version::V0x13,
            params,
        )?;

        // Allocate on heap here to prevent unreachable copies for zeroization
        let mut tag: Box<GenericArray<u8, U32>> = Box::default();
        argon.hash_password_into(
            backup_password.expose_secret(),
            kdf_nonce.as_ref(),
            tag.as_mut(),
        )?;

        let key = KeyMaterial::new(tag)?;
        Ok(RootBackupKey(key))
    }

    pub fn derive_db_backup_dek(&self) -> Result<DataEncryptionKey, Error> {
        // In this scope to prevent being used in other context by accident.
        const DB_BACKUP_DEK_CONTEXT: &str = "\
        org.sealvault.backup.keys.database-backup-data-encryption-key \
        unique suffix: 4dd843f710923a5ce96a974732c42b9b";
        // Make sure nothing is missing due to multiline formatting issues.
        assert!(DB_BACKUP_DEK_CONTEXT.len() >= MIN_BLAKE_CONTEXT_LEN);
        let tag =
            Zeroizing::new(blake3::derive_key(DB_BACKUP_DEK_CONTEXT, self.0.as_ref()));
        let key_material = KeyMaterial::<U32>::from_slice(tag.as_ref())?;
        Ok(DataEncryptionKey::new(
            KeyName::DbBackupDataEncryptionKey,
            key_material,
        ))
    }

    pub fn derive_sk_backup_kek(&self) -> Result<KeyEncryptionKey, Error> {
        const SK_BACKUP_KEK_CONTEXT: &str = "\
        org.sealvault.backup.keys.secret-key-backup-key-encryption-key \
        unique suffix: ced64bf5a8364f2c90424c0efa869a86";
        assert!(SK_BACKUP_KEK_CONTEXT.len() >= MIN_BLAKE_CONTEXT_LEN);
        let tag =
            Zeroizing::new(blake3::derive_key(SK_BACKUP_KEK_CONTEXT, self.0.as_ref()));
        let key_material = KeyMaterial::<U32>::from_slice(tag.as_ref())?;
        Ok(KeyEncryptionKey::new(
            KeyName::SkBackupKeyEncryptionKey,
            key_material,
        ))
    }
}
