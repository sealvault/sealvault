// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    fs::File,
    io::{Read, Write},
    path::{Path, PathBuf},
};

use crate::{
    backup::{
        create::list_backup_dir,
        metadata::{BackupMetadata, MetadataFromFileName},
        setup::{
            backup_connection_pool, rollback_enable_backup, set_up_or_rotate_sk_kek,
        },
        ENCRYPTED_BACKUP_FILE_NAME, METADATA_FILE_NAME,
    },
    db::models as m,
    device::{DeviceIdentifier, OperatingSystem},
    encryption::{
        BackupPassword, EncryptionOutput, KdfNonce, KdfSecret, Keychain, RootBackupKey,
    },
    CoreArgs, CoreError, Error,
};

/// Exposed through FFI to UI.
#[derive(Debug, PartialEq)]
pub struct BackupRestoreData {
    /// Unix timestamp
    pub timestamp: i64,
    /// The device name set by the user.
    pub device_name: String,
    /// The path to the backup.
    pub file_path: String,
}

impl BackupRestoreData {
    fn new(metadata: BackupMetadata, file_path: String) -> Self {
        let BackupMetadata {
            timestamp,
            device_name,
            ..
        } = metadata;
        Self {
            timestamp,
            device_name: device_name.into(),
            file_path,
        }
    }
}

pub fn restore_backup(
    core_args: CoreArgs,
    from_path: String,
    password: String,
) -> Result<(), Error> {
    let keychain = Keychain::new();
    let from_zip = Path::new(&from_path);
    let _ = restore_backup_inner(core_args, from_zip, &password, &keychain)?;
    Ok(())
}

pub(in crate::backup) fn restore_backup_inner(
    core_args: CoreArgs,
    from_zip: &Path,
    password: &str,
    keychain: &Keychain,
) -> Result<BackupMetadata, Error> {
    let password: BackupPassword = password.parse()?;
    let device_id: DeviceIdentifier = core_args.device_id.parse()?;
    let metadata = backup_metadata_from_zip(from_zip)?;

    let kdf_secret = KdfSecret::from_keychain(keychain, &metadata.device_id)?;
    let kdf_nonce: KdfNonce = metadata.kdf_nonce.parse()?;
    let root_backup_key = RootBackupKey::derive_from(&password, &kdf_secret, &kdf_nonce)?;
    let db_backup_dek = root_backup_key.derive_db_backup_dek()?;
    let sk_backup_kek = root_backup_key.derive_sk_backup_kek()?;

    let encrypted_backup_bytes =
        extract_from_zip(from_zip, ENCRYPTED_BACKUP_FILE_NAME).map_err(map_zip_error)?;
    let encryption_output: EncryptionOutput = encrypted_backup_bytes.try_into()?;

    let decrypted_backup = db_backup_dek.decrypt_backup(&encryption_output, &metadata)?;
    let restore_path = Path::new(&core_args.db_file_path);
    restore_decrypted_backup(&metadata, &decrypted_backup, restore_path)?;

    let restored_connection_pool =
        set_up_or_rotate_sk_kek(keychain, &sk_backup_kek, restore_path)?;

    // Disable backup in restored DB and delete keys on device keychain as user will need to
    // generate new backup password for this device.
    rollback_enable_backup(&restored_connection_pool, keychain, &device_id)?;

    Ok(metadata)
}

pub fn find_latest_backup(
    backup_dir: String,
) -> Result<Option<BackupRestoreData>, CoreError> {
    let path = Path::new(&backup_dir);
    let res = find_latest_restorable_backup(path)?;
    Ok(res)
}

pub(in crate::backup) fn find_latest_restorable_backup(
    backup_dir: &Path,
) -> Result<Option<BackupRestoreData>, Error> {
    // Get the current os
    let os: OperatingSystem = Default::default();

    let entries = list_backup_dir(backup_dir)?;
    let mut metas: Vec<(MetadataFromFileName, PathBuf)> = Default::default();
    for entry in entries {
        match MetadataFromFileName::try_from(&entry) {
            Ok(meta) => {
                if meta.os == os {
                    metas.push((meta, entry.path()))
                }
            }
            Err(err) => {
                log::warn!("{}", err);
            }
        }
    }
    metas.sort_by(|a_tup, b_tup| {
        let a = &a_tup.0;
        let b = &b_tup.0;
        a.timestamp
            .cmp(&b.timestamp)
            .then(a.backup_version.cmp(&b.backup_version))
            // Break ties across devices based on device id which is random.
            .then(a.device_id.cmp(&b.device_id))
    });

    if let Some((_, file_path)) = metas.last() {
        let metadata = backup_metadata_from_zip(file_path.as_path())?;
        let file_path = file_path.to_str().ok_or_else(|| Error::Fatal {
            error: "Invalid characters in backup file path".into(),
        })?;
        // Metadata will be authenticated when backup is decrypted on restore
        let restore_data = BackupRestoreData::new(metadata, file_path.into());
        Ok(Some(restore_data))
    } else {
        Ok(None)
    }
}

pub(in crate::backup) fn backup_metadata_from_zip(
    zip_path: &Path,
) -> Result<BackupMetadata, Error> {
    let backup_metadata_bytes =
        extract_from_zip(zip_path, METADATA_FILE_NAME).map_err(map_zip_error)?;
    let metadata: BackupMetadata = serde_json::from_slice(&backup_metadata_bytes)
        .map_err(|_err| Error::Retriable {
            error: "Failed to deserialize backup metadata".into(),
        })?;
    Ok(metadata)
}

fn restore_decrypted_backup(
    metadata: &BackupMetadata,
    decrypted_backup: &[u8],
    to_path: &Path,
) -> Result<(), Error> {
    let mut restored_file = File::create(to_path).map_err(|err| Error::Retriable {
        error: format!("Failed to create restored backup file with error: '{err}'"),
    })?;
    restored_file
        .write_all(decrypted_backup)
        .map_err(|err| Error::Retriable {
            error: format!("Failed to write to restored backup file with error: '{err}'"),
        })?;
    verify_backup(to_path, metadata.backup_version)?;
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

fn map_zip_error(err: zip::result::ZipError) -> Error {
    Error::Retriable {
        error: format!("Failed to restore backup zip with error: '{err}'"),
    }
}

pub(in crate::backup) fn verify_backup(
    backup_path: &Path,
    expected_backup_version: i64,
) -> Result<(), Error> {
    let backup_cp = backup_connection_pool(backup_path)?;

    let mut conn = backup_cp.connection()?;
    let backup_version = m::LocalSettings::fetch_backup_version(&mut conn)?;

    if backup_version == expected_backup_version {
        Ok(())
    } else {
        Err(Error::Fatal {
            error: format!(
                "Expected backup version to be {expected_backup_version} in backup, instead it is: \
                {backup_version}"
            ),
        })
    }
}
