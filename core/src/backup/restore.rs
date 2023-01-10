// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    fs::File,
    io::{Read, Write},
    path::{Path, PathBuf},
    str::FromStr,
};

use tempfile::TempDir;

use crate::{
    backup::{
        metadata::{BackupMetadata, MetadataFromFileName},
        setup::{
            backup_connection_pool, rollback_enable_backup, set_up_or_rotate_sk_kek,
        },
        BackupError, BackupStorageI, BackupVersion, ENCRYPTED_BACKUP_FILE_NAME,
        METADATA_FILE_NAME,
    },
    db::models as m,
    device::{DeviceIdentifier, OperatingSystem},
    encryption::{
        BackupPassword, EncryptionOutput, KdfNonce, KdfSecret, Keychain, RootBackupKey,
    },
    utils::path_to_string,
    CoreArgs, CoreError, Error,
};

/// Exposed through FFI to UI.
#[derive(Debug, PartialEq)]
pub struct BackupRestoreData {
    /// Unix timestamp
    pub timestamp: i64,
    /// The device name set by the user.
    pub device_name: String,
    /// The backup file name in backup storage.
    pub backup_file_name: String,
}

impl BackupRestoreData {
    fn new(metadata: BackupMetadata, backup_file_name: String) -> Self {
        let BackupMetadata {
            timestamp,
            device_name,
            ..
        } = metadata;
        Self {
            timestamp,
            device_name: device_name.into(),
            backup_file_name,
        }
    }
}

#[derive(Debug)]
pub(in crate::backup) struct RestoreWorkDir {
    // The `TempDir` is not accessed, but we want to retain for the life time of this struct,
    // as it's destroyed on drop.
    #[allow(dead_code)]
    tmp_dir: TempDir,
    zip_path: PathBuf,
}

impl RestoreWorkDir {
    pub fn new(backup_file_name: &str) -> Result<Self, Error> {
        let tmp_dir = tempfile::tempdir().map_err(|err| Error::Retriable {
            error: err.to_string(),
        })?;
        let zip_path = tmp_dir.path().join(Path::new(backup_file_name));
        Ok(Self { tmp_dir, zip_path })
    }

    pub fn zip_path(&self) -> &Path {
        self.zip_path.as_path()
    }

    pub fn zip_path_string(&self) -> Result<String, Error> {
        path_to_string(self.zip_path())
    }
}

pub fn restore_backup(
    core_args: CoreArgs,
    backup_storage: Box<dyn BackupStorageI>,
    backup_file_name: String,
    password: String,
) -> Result<(), BackupError> {
    let keychain = Keychain::new();
    let _ = restore_backup_inner(
        core_args,
        &*backup_storage,
        backup_file_name,
        &keychain,
        &password,
    )?;
    Ok(())
}

pub(in crate::backup) fn restore_backup_inner(
    core_args: CoreArgs,
    backup_storage: &dyn BackupStorageI,
    backup_file_name: String,
    keychain: &Keychain,
    password: &str,
) -> Result<BackupMetadata, BackupError> {
    let password: BackupPassword = password.parse().map_err(|err| {
        log::debug!("Error parsing backup password: {err}");
        BackupError::InvalidPassword
    })?;

    let device_id: DeviceIdentifier = core_args.device_id.parse()?;
    let work_dir = RestoreWorkDir::new(&backup_file_name)?;

    if !backup_storage.copy_from_storage(backup_file_name, work_dir.zip_path_string()?) {
        return Err(BackupError::FailedToFetchBackup);
    }

    let metadata = backup_metadata_from_zip(work_dir.zip_path())?;

    let kdf_secret =
        KdfSecret::from_keychain(keychain, &metadata.device_id).map_err(|err| {
            log::debug!("Error fetching KDF secret from keychain: {err}");
            BackupError::KDFSecretNotAvailable
        })?;

    let kdf_nonce: KdfNonce = metadata.kdf_nonce.parse()?;
    let root_backup_key = RootBackupKey::derive_from(&password, &kdf_secret, &kdf_nonce)?;
    let db_backup_dek = root_backup_key.derive_db_backup_dek()?;
    let sk_backup_kek = root_backup_key.derive_sk_backup_kek()?;

    let encrypted_backup_bytes =
        extract_from_zip(work_dir.zip_path(), ENCRYPTED_BACKUP_FILE_NAME)
            .map_err(map_zip_error)?;
    let encryption_output: EncryptionOutput = encrypted_backup_bytes.try_into()?;

    let decrypted_backup = db_backup_dek
        .decrypt_backup(&encryption_output, &metadata)
        .map_err(|err| {
            log::debug!("Error decrypting backup: {err}");
            // It might be possible that the KDF secret is invalid if there is a logic error in the
            // application or the keychain provides the wrong secret, but in the absence of bugs, the
            // error is due to the user providing the wrong password.
            BackupError::InvalidPassword
        })?;
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
    backup_storage: Box<dyn BackupStorageI>,
) -> Result<Option<BackupRestoreData>, CoreError> {
    let res = find_latest_backup_inner(&*backup_storage)?;
    Ok(res)
}

pub(in crate::backup) fn find_latest_backup_inner(
    backup_storage: &dyn BackupStorageI,
) -> Result<Option<BackupRestoreData>, BackupError> {
    // Get the current os
    let os: OperatingSystem = Default::default();

    // Gather backup metadata from backups created on the same OS.
    // We might relax restricting to the same OS in the future.
    let mut metas: Vec<(MetadataFromFileName, String)> = Default::default();
    for backup_file_name in backup_storage.list_backup_file_names() {
        match MetadataFromFileName::from_str(&backup_file_name) {
            Ok(meta) => {
                if meta.os == os {
                    metas.push((meta, backup_file_name))
                }
            }
            Err(err) => log::warn!("Error parsing backup file name: '{err}'"),
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

    let last_el: Option<(_, _)> = if metas.is_empty() {
        None
    } else {
        Some(metas.swap_remove(metas.len() - 1))
    };

    if let Some((_, backup_file_name)) = last_el {
        let work_dir = RestoreWorkDir::new(&backup_file_name)?;
        let success = backup_storage
            .copy_from_storage(backup_file_name.clone(), work_dir.zip_path_string()?);
        if !success {
            return Err(BackupError::FailedToFetchBackup);
        }
        let metadata = backup_metadata_from_zip(work_dir.zip_path())?;
        // Metadata will be authenticated when backup is decrypted on restore
        let restore_data = BackupRestoreData::new(metadata, backup_file_name);
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
    expected_backup_version: BackupVersion,
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
