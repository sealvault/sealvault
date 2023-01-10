// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::{CoreError, Error};

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum BackupError {
    #[error("Backup is disabled.")]
    BackupDisabled,

    #[error("Failed to put backup file into backup storage.")]
    FailedToStoreBackup,

    #[error("Failed to fetch the backup file from backup storage.")]
    FailedToFetchBackup,

    #[error("Failed to delete a backup file from backup storage.")]
    FailedToDeleteBackup,

    #[error("Invalid password for backup.")]
    InvalidPassword,

    #[error("The KDF secret is not available from the keychain.")]
    KDFSecretNotAvailable,

    /// See crate::error;
    #[error("{error}")]
    Error { error: CoreError },
}

impl From<Error> for BackupError {
    fn from(error: Error) -> Self {
        let error: CoreError = error.into();
        Self::Error { error }
    }
}

impl From<BackupError> for Error {
    fn from(error: BackupError) -> Self {
        match error {
            BackupError::Error { error } => error.into(),
            error => Error::Retriable {
                error: error.to_string(),
            },
        }
    }
}

impl From<BackupError> for CoreError {
    fn from(error: BackupError) -> Self {
        let error: Error = error.into();
        error.into()
    }
}

impl From<CoreError> for BackupError {
    fn from(error: CoreError) -> Self {
        let error: Error = error.into();
        error.into()
    }
}
