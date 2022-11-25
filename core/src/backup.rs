// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
use std::{
    fs::File,
    io::{Read, Seek, Write},
    path::{Path, PathBuf},
};

use diesel::connection::SimpleConnection;
use olpc_cjson::CanonicalFormatter;
use serde::{Deserialize, Serialize};
use tempfile::NamedTempFile;
use typed_builder::TypedBuilder;

use crate::{
    db::{models as m, ConnectionPool},
    device::{DeviceIdentifier, OperatingSystem},
    encryption::{
        BackupPassword, DataEncryptionKey, EncryptionOutput, KdfNonce, KdfSecret,
        KeyEncryptionKey, KeyName, Keychain, RootBackupKey,
    },
    utils::unix_timestamp,
    Error,
};

// File names inside the backup zip
const ENCRYPTED_BACKUP_FILE_NAME: &str = "backup.sqlite3.encrypted";
const METADATA_FILE_NAME: &str = "metadata.json";

/// The backup scheme version.
#[derive(
    Copy,
    Clone,
    Debug,
    Hash,
    PartialEq,
    Eq,
    strum_macros::AsRefStr,
    strum_macros::Display,
    strum_macros::EnumString,
    strum_macros::EnumIter,
    Serialize,
    Deserialize,
)]
#[strum(serialize_all = "lowercase")]
pub enum BackupVersion {
    V1,
}

/// Saved as a plaintext json file along with the encrypted backup.
/// More info: https://sealvault.org/dev-docs/design/backup/#backup-contents
#[derive(Debug, PartialEq, Serialize, Deserialize, TypedBuilder)]
pub struct BackupMetadata {
    /// The backup implementation version
    backup_scheme_version: BackupVersion,
    /// The backup version from the database. Monotonically increasing integer within a device.
    backup_version: i32,
    /// Unix timestamp
    #[builder(default_code = "unix_timestamp()")]
    timestamp: i64,
    device_identifier: DeviceIdentifier,
    #[builder(default)]
    operating_system: OperatingSystem,
    /// Base-64 encoded KDF nonce
    #[builder(setter(transform = |k: &KdfNonce| base64::encode(k)))]
    kdf_nonce: String,
}

impl BackupMetadata {
    fn backup_file_name(&self) -> PathBuf {
        format!(
            "sealvault_backup_{}_{}_{}_{}_{}.zip",
            self.backup_scheme_version,
            self.operating_system,
            self.timestamp,
            self.device_identifier,
            self.backup_version
        )
        .into()
    }

    /// Use this for a canonical serialization of the backup metadata to make sure that the
    /// associated data in the AEAD matches.
    pub fn canonical_json(&self) -> Result<Vec<u8>, Error> {
        let mut buf = Vec::new();
        let mut ser =
            serde_json::Serializer::with_formatter(&mut buf, CanonicalFormatter::new());
        self.serialize(&mut ser).map_err(|_| Error::Fatal {
            error: "Failed to serialize backup metadata.".into(),
        })?;
        Ok(buf)
    }
}

/// Set up backup keys for the user and return the backup password that can be displayed to the
/// user.
pub fn set_up_backup(
    connection_pool: &ConnectionPool,
    keychain: &Keychain,
) -> Result<String, Error> {
    // In an exclusive transaction to prevent running in parallel and potentially ending up with
    // mixed up keychain items.
    connection_pool.exclusive_transaction(|mut tx_conn| {
        let backup_password = BackupPassword::setup(keychain)?;
        let kdf_secret = KdfSecret::setup(keychain)?;
        let kdf_nonce: KdfNonce = KdfNonce::random()?;

        let root_backup_key =
            RootBackupKey::derive_from(&backup_password, &kdf_secret, &kdf_nonce)?;

        let db_backup_dek = root_backup_key.derive_db_backup_dek()?;
        db_backup_dek.save_to_local_keychain(keychain)?;

        let sk_backup_kek = root_backup_key.derive_sk_backup_kek()?;

        let sk_kek = KeyEncryptionKey::sk_kek(keychain)?;

        // Fetch secret key data encryption key (SK-DEK) from DB and decrypt it with secret key
        // encryption key (SK-KEK) from local keychain.
        let (sk_dek_id, sk_dek) = m::DataEncryptionKey::fetch_dek(
            tx_conn.as_mut(),
            KeyName::SkDataEncryptionKey,
            &sk_kek,
        )?;

        // Encrypt SK-DEK with the secret key backup encryption key and save the encrypted SK-DEK in
        // the database.
        let encrypted_sk_dek = sk_dek.to_encrypted(&sk_backup_kek)?;
        m::NewLocalEncryptedDek::builder()
            .dek_id(&sk_dek_id)
            .encrypted_dek(&encrypted_sk_dek)
            .kek_name(sk_backup_kek.name())
            .build()
            .insert(tx_conn.as_mut())?;

        // Update timestamps
        m::LocalSettings::set_backup_kdf_nonce(tx_conn.as_mut(), &kdf_nonce)?;
        m::LocalSettings::update_backup_password_timestamp(tx_conn.as_mut())?;

        Ok(backup_password.display_to_user())
    })
}

/// Create backup to the desired directory if needed. The directory is assumed to exist.
/// Returns the backup metadata if a backup was created.
/// A backup is needed if the pending backup version matches the completed backup version in the
/// database.
/// The backup is a zip file that contains an encrypted database backup and the metadata. Returns
/// the path to the zip file. More info:
/// https://sealvault.org/dev-docs/design/backup/#backup-contents
pub fn create_backup(
    connection_pool: &ConnectionPool,
    keychain: &Keychain,
    device_identifier: DeviceIdentifier,
    out_dir: &Path,
) -> Result<Option<BackupMetadata>, Error> {
    if let Some(metadata) =
        db_backup(connection_pool, keychain, device_identifier, out_dir)?
    {
        // TODO clean up old versions
        Ok(Some(metadata))
    } else {
        Ok(None)
    }
}

pub fn restore_backup(
    db_backup_dek: &DataEncryptionKey,
    from_zip: &Path,
    to_path: &Path,
) -> Result<BackupMetadata, Error> {
    let backup_metadata_bytes =
        extract_from_zip(from_zip, METADATA_FILE_NAME).map_err(map_zip_error)?;

    let metadata: BackupMetadata = serde_json::from_slice(&backup_metadata_bytes)
        .map_err(|_err| Error::Retriable {
            error: "Failed to deserialize backup metadata".into(),
        })?;
    let encrypted_backup_bytes =
        extract_from_zip(from_zip, ENCRYPTED_BACKUP_FILE_NAME).map_err(map_zip_error)?;

    let encryption_output: EncryptionOutput = encrypted_backup_bytes.try_into()?;

    let decrypted_backup = db_backup_dek.decrypt_backup(&encryption_output, &metadata)?;

    let mut restored_file = File::create(to_path).map_err(|err| Error::Retriable {
        error: format!("Failed to create restored backup file with error: '{err}'"),
    })?;
    restored_file
        .write_all(&decrypted_backup)
        .map_err(|err| Error::Retriable {
            error: format!("Failed to write to restored backup file with error: '{err}'"),
        })?;
    verify_backup(to_path, metadata.backup_version)?;

    Ok(metadata)
}

pub fn rotate_backup_password() {
    // Hold exclusive transaction to make sure no backup is in progress with different key
    todo!()
}

fn db_backup(
    connection_pool: &ConnectionPool,
    keychain: &Keychain,
    device_identifier: DeviceIdentifier,
    out_dir: &Path,
) -> Result<Option<BackupMetadata>, Error> {
    // Flush WAL to the DB file. Can't be inside exclusive transaction, because it acquires its own
    // lock.
    let mut conn = connection_pool.connection()?;
    // We check this twice to avoid running the expensive wal checkpointing if a backup is not
    // needed.
    if !m::LocalSettings::needs_backup(&mut conn)? {
        return Ok(None);
    }
    conn.batch_execute("PRAGMA wal_checkpoint(FULL);")?;

    connection_pool.exclusive_transaction(|mut tx_conn| {
        if !m::LocalSettings::needs_backup(tx_conn.as_mut())? {
            return Ok(None);
        }

        // Fetch these while holding the exclusive lock to make sure they match
        // the secret key backup encryption key that was used to encrypt the secret key data
        // encryption key which is stored inside the DB.
        let backup_version =
            m::LocalSettings::fetch_pending_backup_version(tx_conn.as_mut())?;
        let kdf_nonce =
            m::LocalSettings::fetch_kdf_nonce(tx_conn.as_mut())?.ok_or_else(|| {
                Error::Fatal {
            error: "No KDF nonce in DB. Make sure backup is set up before attempting to \
                    create one.".into()
        }
            })?;
        let db_backup_dek = DataEncryptionKey::db_backup_dek(keychain)?;

        let backup_contents =
            create_verified_backup(connection_pool.db_path(), backup_version)?;

        let metadata = BackupMetadata::builder()
            .backup_scheme_version(BackupVersion::V1)
            .backup_version(backup_version)
            .device_identifier(device_identifier)
            .kdf_nonce(&kdf_nonce)
            .build();

        let encryption_output =
            db_backup_dek.encrypt_backup(&backup_contents, &metadata)?;

        create_backup_zip(out_dir, &metadata, &encryption_output)?;

        m::LocalSettings::set_completed_backup_version(tx_conn.as_mut(), backup_version)?;

        Ok(Some(metadata))
    })
}

/// Create a verified backup of the DB and return it as bytes.
fn create_verified_backup(db_path: &Path, backup_version: i32) -> Result<Vec<u8>, Error> {
    let mut db_file = File::open(db_path).map_err(|err| Error::Retriable {
        error: format!("Failed to open DB file: {err}"),
    })?;

    let mut backup_file = NamedTempFile::new().map_err(|err| Error::Retriable {
        error: format!("Failed to create temporary file with error: '{err}'"),
    })?;

    // Sqlite C backup api would be preferable to copying, but it's not supported by Diesel.
    // Copy while holding lock to make sure DB doesn't change.
    std::io::copy(&mut db_file, &mut backup_file).map_err(|err| Error::Retriable {
        error: format!("Failed to copy DB file to backup file: {err}"),
    })?;

    verify_backup(backup_file.path(), backup_version)?;

    let mut backup_contents: Vec<u8> = Vec::new();
    backup_file.rewind().map_err(|err| Error::Retriable {
        error: format!("Failed to move cursor to start of file with error: '{err}'"),
    })?;
    backup_file
        .read_to_end(&mut backup_contents)
        .map_err(|err| Error::Retriable {
            error: format!("Failed to read backup file contents with error: '{err}'"),
        })?;

    Ok(backup_contents)
}

fn create_backup_zip(
    out_dir: &Path,
    metadata: &BackupMetadata,
    encryption_output: &EncryptionOutput,
) -> Result<(), Error> {
    let out_path = out_dir.join(metadata.backup_file_name());
    // Overwrites existing file which is important to rerun if setting the completed backup
    // version fails.
    let out_file = File::create(out_path).map_err(|err| Error::Retriable {
        error: format!("Failed to create backup archive file with error: '{err}'"),
    })?;

    let meta_ser = metadata.canonical_json()?;

    create_backup_zip_inner(out_file, encryption_output, &meta_ser)
        .map_err(map_zip_error)?;

    Ok(())
}

fn map_zip_error(err: zip::result::ZipError) -> Error {
    Error::Retriable {
        error: format!("Failed to create backup zip with error: '{err}'"),
    }
}

fn create_backup_zip_inner(
    out_file: File,
    encryption_output: &EncryptionOutput,
    metadata_serialized: &[u8],
) -> Result<(), zip::result::ZipError> {
    use zip::{write::FileOptions, CompressionMethod, ZipWriter};

    let mut zip_file = ZipWriter::new(out_file);
    // No compression as the backup is encrypted which doesn't compress much.
    let zip_options =
        FileOptions::default().compression_method(CompressionMethod::Stored);

    zip_file.start_file(ENCRYPTED_BACKUP_FILE_NAME, zip_options)?;
    // Includes the nonce
    let encrypted_bytes: Vec<u8> = encryption_output.into();
    zip_file.write_all(&encrypted_bytes)?;

    let zip_options =
        FileOptions::default().compression_method(CompressionMethod::Stored);
    zip_file.start_file(METADATA_FILE_NAME, zip_options)?;
    zip_file.write_all(metadata_serialized)?;

    zip_file.finish()?;

    Ok(())
}

fn extract_from_zip(
    path: &Path,
    file_name: &str,
) -> Result<Vec<u8>, zip::result::ZipError> {
    let file = File::open(path)?;
    let mut archive = zip::ZipArchive::new(file)?;

    let mut file_bytes: Vec<u8> = Default::default();
    let mut backup_file = archive.by_name(file_name)?;
    backup_file.read_to_end(&mut file_bytes)?;

    Ok(file_bytes)
}

fn verify_backup(backup_path: &Path, expected_backup_version: i32) -> Result<(), Error> {
    let backup_path = backup_path.to_str().ok_or_else(|| Error::Fatal {
        error: "Failed to convert backup path to utf-8".into(),
    })?;
    let backup_cp = ConnectionPool::new(backup_path)?;
    let mut backup_conn = backup_cp.connection()?;

    let pending_backup_version =
        m::LocalSettings::fetch_pending_backup_version(&mut backup_conn)?;
    if pending_backup_version == expected_backup_version {
        Ok(())
    } else {
        Err(Error::Fatal {
            error: format!(
                "Expected pending backup version to be {expected_backup_version} in \
                            backup, instead it is: {pending_backup_version}"
            ),
        })
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use anyhow::Result;

    use super::*;
    use crate::{
        db::{data_migrations, schema_migrations::run_migrations},
        encryption::Keychain,
        public_suffix_list::PublicSuffixList,
    };

    #[test]
    fn db_backup() -> Result<()> {
        let device_identifier: DeviceIdentifier = "test-device".to_string().try_into()?;
        let tmp_dir = tempfile::tempdir().expect("creates temp dir");
        let backup_dir = tmp_dir.path().join("backups");
        fs::create_dir(backup_dir.as_path())?;
        let db_path = tmp_dir.path().join("db.sqlite3");

        // Create mock db
        let connection_pool = ConnectionPool::new(db_path.to_str().expect("ok utf-8"))?;
        let keychain = Keychain::new();
        let psl = PublicSuffixList::new()?;
        connection_pool.exclusive_transaction(|mut tx_conn| {
            run_migrations(&mut tx_conn)?;
            data_migrations::run_all(tx_conn, &keychain, &psl)
        })?;

        let password = set_up_backup(&connection_pool, &keychain)?;

        let metadata = create_backup(
            &connection_pool,
            &keychain,
            device_identifier,
            backup_dir.as_path(),
        )?
        .expect("needs backup");

        let password: BackupPassword = password.parse()?;
        let kdf_secret = KdfSecret::from_keychain(&keychain)?;
        let kdf_nonce: KdfNonce = metadata.kdf_nonce.parse()?;
        let root_backup_key =
            RootBackupKey::derive_from(&password, &kdf_secret, &kdf_nonce)?;
        let db_backup_dek = root_backup_key.derive_db_backup_dek()?;

        let restore_from = backup_dir.join(metadata.backup_file_name());
        let restore_to = NamedTempFile::new()?;
        let backup_metadata =
            restore_backup(&db_backup_dek, restore_from.as_path(), restore_to.path())?;

        assert_eq!(metadata, backup_metadata);

        Ok(())
    }
}
