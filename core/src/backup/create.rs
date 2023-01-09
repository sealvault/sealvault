// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    fs::File,
    io::{Read, Seek, Write},
    path::Path,
    str::FromStr,
};

use diesel::connection::SimpleConnection;

use crate::{
    backup::{
        backup_error::BackupError, backup_scheme::BackupScheme,
        metadata::MetadataFromFileName, restore::verify_backup, BackupMetadata,
        BackupStorageI, BackupVersion,
    },
    db::models as m,
    encryption::{DataEncryptionKey, EncryptionOutput},
    resources::CoreResourcesI,
    utils::{path_to_string, tmp_file},
    Error,
};

/// Create backup to the desired directory if needed. The directory is assumed to exist.
/// Returns the backup metadata if a backup was created.
/// A backup is needed if the pending backup version matches the completed backup version in the
/// database.
/// The backup is a zip file that contains an encrypted database backup and the metadata. Returns
/// the path to the zip file. More info:
/// https://sealvault.org/dev-docs/design/backup/#backup-contents
pub fn create_backup(
    resources: &dyn CoreResourcesI,
) -> Result<BackupMetadata, BackupError> {
    if !resources.backup_storage().can_backup() {
        return Err(BackupError::BackupDisabled);
    }
    let metadata = db_backup(resources)?;
    remove_outdated_backups(resources.backup_storage(), &metadata)?;
    Ok(metadata)
}

pub(in crate::backup) fn db_backup(
    resources: &dyn CoreResourcesI,
) -> Result<BackupMetadata, Error> {
    let connection_pool = resources.connection_pool();

    // Flush WAL to the DB file. Can't be inside exclusive transaction, because it acquires its own
    // lock.
    let mut conn = connection_pool.connection()?;
    // Increment here to make sure it's part of backup. If there is an error later, it'll cause
    // gaps in the backup versions, but that's ok.
    m::LocalSettings::increment_backup_version(&mut conn)?;
    conn.batch_execute("PRAGMA wal_checkpoint(FULL);")?;

    // Exclusive transaction here for copy
    connection_pool.exclusive_transaction(|mut tx_conn| {
        let backup_version = m::LocalSettings::fetch_backup_version(tx_conn.as_mut())?;

        // Fetch these while holding the exclusive lock to make sure they match
        // the secret key backup encryption key that was used to encrypt the secret key data
        // encryption key which is stored inside the DB.
        let kdf_nonce =
            m::LocalSettings::fetch_kdf_nonce(tx_conn.as_mut())?.ok_or_else(|| {
                Error::Fatal {
                error:
                    "No KDF nonce in DB. Make sure backup is set up before attempting \
                        to create one."
                        .into(),
            }
            })?;
        let db_backup_dek = DataEncryptionKey::db_backup_dek(resources.keychain())?;

        // Copies DB file
        let backup_contents =
            create_verified_backup(connection_pool.db_path(), backup_version)?;

        let metadata = BackupMetadata::builder()
            .backup_scheme(BackupScheme::V1)
            .backup_version(backup_version)
            .device_id(resources.device_id().clone())
            .device_name(resources.device_name().clone())
            .kdf_nonce(&kdf_nonce)
            .build();

        let encryption_output =
            db_backup_dek.encrypt_backup(&backup_contents, &metadata)?;

        store_backup_zip(resources.backup_storage(), &metadata, &encryption_output)?;

        m::LocalSettings::update_backup_timestamp(tx_conn.as_mut())?;

        Ok(metadata)
    })
}

/// Create a verified backup of the DB and return it as bytes.
fn create_verified_backup(
    db_path: &Path,
    backup_version: BackupVersion,
) -> Result<Vec<u8>, Error> {
    let mut db_file = File::open(db_path).map_err(|err| Error::Retriable {
        error: format!("Failed to open DB file: {err}"),
    })?;

    let mut backup_file = tmp_file()?;

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

fn store_backup_zip(
    backup_storage: &dyn BackupStorageI,
    metadata: &BackupMetadata,
    encryption_output: &EncryptionOutput,
) -> Result<(), BackupError> {
    let mut tmp_file = tmp_file()?;

    let meta_ser = metadata.canonical_json()?;
    create_backup_zip(tmp_file.as_file_mut(), encryption_output, &meta_ser)
        .map_err(map_zip_error)?;

    let tmp_file_path = path_to_string(tmp_file.path())?;

    let is_ok =
        backup_storage.copy_to_storage(metadata.backup_file_name(), tmp_file_path);
    if is_ok {
        Ok(())
    } else {
        Err(BackupError::FailedToStoreBackup)
    }
}

/// Removes the outdated backups that were created on this device.
fn remove_outdated_backups(
    backup_storage: &dyn BackupStorageI,
    current_metadata: &BackupMetadata,
) -> Result<(), BackupError> {
    let backup_file_names = backup_storage.list_backup_file_names();
    for file_name in backup_file_names {
        if should_delete(&file_name, current_metadata)? {
            let is_ok = backup_storage.delete_backup(file_name);
            if !is_ok {
                log::error!("Failed to delete backup file.")
            }
        }
    }
    Ok(())
}

fn should_delete(
    backup_file_name: &str,
    current_metadata: &BackupMetadata,
) -> Result<bool, Error> {
    let meta_from_file_name = match MetadataFromFileName::from_str(backup_file_name) {
        Ok(meta) => meta,
        Err(err) => {
            log::debug!("Error on should delete file in backup dir: {err}");
            // If it's not a backup file, we shouldn't delete it.
            return Ok(false);
        }
    };

    // There may be other devices saving backups in the same directory.
    let same_device = meta_from_file_name.device_id == current_metadata.device_id;
    // Important to only delete earlier versions as a newer backup may have been created inbetween.
    let earlier_version =
        meta_from_file_name.backup_version < current_metadata.backup_version;
    Ok(same_device && earlier_version)
}

fn create_backup_zip(
    out_file: &mut File,
    encryption_output: &EncryptionOutput,
    metadata_serialized: &[u8],
) -> Result<(), zip::result::ZipError> {
    use zip::{write::FileOptions, CompressionMethod, ZipWriter};

    use crate::backup::{ENCRYPTED_BACKUP_FILE_NAME, METADATA_FILE_NAME};

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
fn map_zip_error(err: zip::result::ZipError) -> Error {
    Error::Retriable {
        error: format!("Failed to create backup zip with error: '{err}'"),
    }
}
