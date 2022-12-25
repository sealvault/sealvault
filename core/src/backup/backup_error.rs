// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::{CoreError, Error};

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum BackupError {
    #[error("The backup directory is not available.")]
    BackupDirectoryNotAvailable,

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
            BackupError::BackupDirectoryNotAvailable => Error::Fatal {
                error: error.to_string(),
            },
            BackupError::Error { error } => error.into(),
        }
    }
}

impl From<BackupError> for CoreError {
    fn from(error: BackupError) -> Self {
        let error: Error = error.into();
        error.into()
    }
}
