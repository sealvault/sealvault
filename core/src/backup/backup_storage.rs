// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

/// Abstraction over the synced backup storage.
/// Implementation injected on iOS from Swift for iCloud Storage.
pub trait BackupStorageI: Send + Sync + Debug {
    /// Whether synced backup storage is available.
    fn can_backup(&self) -> bool;

    /// List of backup file names in backup storage.
    fn list_backup_file_names(&self) -> Vec<String>;

    /// Copy a backup file to the storage with the desired backup file name.
    /// The first argument should be the file name by which the backup file should be stored in
    /// backup storage.
    /// The second argument should be an absolute path to a temporary file in the local storage of
    /// the device.
    /// Returns true if the operation succeeded, false otherwise.
    fn copy_to_storage(&self, backup_file_name: String, tmp_file_path: String) -> bool;

    /// Download a file from backup storage to the desired path.
    /// The operation may involve network I/O.
    /// Returns true if the operation succeeded, false otherwise.
    fn copy_from_storage(&self, backup_file_name: String, to_file_path: String) -> bool;

    /// Delete a backup by its file name from backup storage.
    /// Returns true if the operation succeeded, false otherwise.
    fn delete_backup(&self, backup_file_name: String) -> bool;
}

/// A backup storage implementation that stores files in a temporary directory on the device.
/// The temporary directory is discarded when the struct is dropped.
/// Used for testing.
#[cfg(test)]
pub(crate) mod tmp_backup_storage {
    use std::{fmt::Debug, fs, path::PathBuf};

    use tempfile::TempDir;

    use crate::{backup::backup_storage::BackupStorageI, Error};

    #[derive(Debug)]
    pub struct TmpBackupStorage {
        pub tmp_dir: TempDir,
        can_backup: bool,
    }

    impl TmpBackupStorage {
        pub fn new(can_backup: bool) -> Result<Self, Error> {
            let tmp_dir = tempfile::tempdir().map_err(|err| Error::Fatal {
                error: err.to_string(),
            })?;
            Ok(Self {
                tmp_dir,
                can_backup,
            })
        }
    }

    impl Default for TmpBackupStorage {
        fn default() -> Self {
            Self::new(true).expect("can create temp dir")
        }
    }

    impl BackupStorageI for TmpBackupStorage {
        fn can_backup(&self) -> bool {
            self.can_backup
        }

        fn list_backup_file_names(&self) -> Vec<String> {
            let entries =
                fs::read_dir(self.tmp_dir.path()).expect("can list tmp directory");

            let mut results: Vec<String> = Default::default();
            for entry_res in entries {
                match entry_res {
                    Ok(entry) => {
                        let file_name = entry
                            .file_name()
                            .into_string()
                            .expect("file name is valid string");
                        results.push(file_name);
                    }
                    Err(err) => {
                        // If the file was removed between listing accessing, that's ok.
                        if err.kind() != std::io::ErrorKind::NotFound {
                            log::error!(
                                "Failed to access backup file due to error: {err}"
                            );
                        }
                    }
                };
            }
            results
        }

        fn copy_to_storage(
            &self,
            backup_file_name: String,
            tmp_file_path: String,
        ) -> bool {
            let backup_file_name: PathBuf = backup_file_name.into();
            let to_path: PathBuf = self.tmp_dir.path().join(backup_file_name);

            let tmp_file_path: PathBuf = tmp_file_path.into();

            match fs::copy(tmp_file_path.as_path(), to_path.as_path()) {
                Ok(_) => true,
                Err(err) => {
                    log::error!(
                        "Error copying file '{tmp_file_path:?}' to storage: '{err}'"
                    );
                    false
                }
            }
        }

        fn copy_from_storage(
            &self,
            backup_file_name: String,
            to_file_path: String,
        ) -> bool {
            let to_file_path: PathBuf = to_file_path.into();
            let backup_file_name: PathBuf = backup_file_name.into();
            let from_file_path = self.tmp_dir.path().join(backup_file_name.as_path());
            match fs::copy(from_file_path.as_path(), to_file_path.as_path()) {
                Ok(_) => true,
                Err(err) => {
                    log::error!(
                        "Error copying backup file '{backup_file_name:?}' to path \
                        '{to_file_path:?}': '{err}'"
                    );
                    false
                }
            }
        }

        fn delete_backup(&self, backup_file_name: String) -> bool {
            let backup_file_name: PathBuf = backup_file_name.into();
            let file_path = self.tmp_dir.path().join(backup_file_name.as_path());
            match fs::remove_file(file_path.as_path()) {
                Ok(_) => true,
                Err(err) => {
                    dbg!(&err);
                    dbg!(&backup_file_name);
                    log::error!("Error '{err}' deleting file: '{backup_file_name:?}'");
                    false
                }
            }
        }
    }
}
