// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use generic_array::ArrayLength;

#[cfg(not(target_os = "ios"))]
use crate::encryption::keychains::in_memory_keychain::InMemoryKeychain;
#[cfg(target_os = "ios")]
use crate::encryption::keychains::ios_keychain::IOSKeychain;
use crate::{
    device::DeviceIdentifier,
    encryption::{key_material::KeyMaterial, KeyName},
    Error,
};

/// Keychain to securely store secrets on the operating system.
/// Injected by the host language as a Uniffi callback interface.
/// More info: https://mozilla.github.io/uniffi-rs/udl/callback_interfaces.html
///
/// The methods takes ownership of the `KeyEncryptionKey` because on iOS, the Core Foundation
/// function (`CFData::from_arc`) that lets us pass the buffer to the iOS Keychain without an
/// internal copy needs to take ownership of the buffer.
pub(super) trait KeychainImpl: Debug + Send + Sync {
    /// Get an item from the local keychain.
    fn get_local<N: ArrayLength<u8>>(
        &self,
        name: KeyName,
    ) -> Result<KeyMaterial<N>, KeychainError>;

    fn get_synced<N: ArrayLength<u8>>(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
    ) -> Result<KeyMaterial<N>, KeychainError>;

    /// Delete an item from the local keychain.
    fn delete_local(&self, name: KeyName) -> Result<(), KeychainError>;

    /// Delete an item from the synced keychain.
    fn delete_synced(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
    ) -> Result<(), KeychainError>;

    /// Put an item on the local (not-synced) keychain.
    fn upsert_local<N: ArrayLength<u8>>(
        &self,
        name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), KeychainError>;

    /// Add or update an item on the synced keychain.
    fn upsert_synced<N: ArrayLength<u8>>(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), KeychainError>;
}

#[derive(Debug)]
pub struct Keychain {
    // `KeychainImpl` is not object safe, so we can't use `Box<dyn KeychainImpl>`
    #[cfg(target_os = "ios")]
    keychain: IOSKeychain,
    #[cfg(not(target_os = "ios"))]
    keychain: InMemoryKeychain,
}

impl Keychain {
    #[cfg(target_os = "ios")]
    pub fn new() -> Self {
        let keychain = IOSKeychain::new();
        Self { keychain }
    }

    #[cfg(not(target_os = "ios"))]
    pub fn new() -> Self {
        let keychain = InMemoryKeychain::new();
        Self { keychain }
    }

    /// Get a symmetric key from the keychain.
    pub(in crate::encryption) fn get_local<N: ArrayLength<u8>>(
        &self,
        name: KeyName,
    ) -> Result<KeyMaterial<N>, KeychainError> {
        self.keychain.get_local::<N>(name)
    }

    pub(in crate::encryption) fn get_synced<N: ArrayLength<u8>>(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
    ) -> Result<KeyMaterial<N>, KeychainError> {
        self.keychain.get_synced::<N>(device_identifier, name)
    }

    pub(in crate::encryption) fn delete_local_if_exists(
        &self,
        name: KeyName,
    ) -> Result<(), KeychainError> {
        self.keychain
            .delete_local(name)
            .or_else(handle_not_found_for_if_exists)
    }

    pub(in crate::encryption) fn delete_synced_if_exists(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
    ) -> Result<(), KeychainError> {
        self.keychain
            .delete_synced(device_identifier, name)
            .or_else(handle_not_found_for_if_exists)
    }

    /// Add or update an item on the local keychain.
    pub(in crate::encryption) fn upsert_local<N: ArrayLength<u8>>(
        &self,
        name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), KeychainError> {
        self.keychain.upsert_local(name, key)
    }

    /// Add or update an item on the synced keychain.
    pub(in crate::encryption) fn upsert_synced<N: ArrayLength<u8>>(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), KeychainError> {
        self.keychain.upsert_synced(device_identifier, name, key)
    }
}

impl Default for Keychain {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum KeychainError {
    /// Generic application error
    #[error("Application error: {error}")]
    App { error: Error },
    /// The keychain item was not found.
    #[error("Keychain item doesn't exist: '{name}'")]
    NotFound { name: String },
    /// A keychain item by this name already exists.
    #[error("Keychain item already exists: '{name}'")]
    DuplicateItem { name: String },
    /// Failed to get item with error code.
    #[error("Failed to get keychain item '{name}' due to error {code}")]
    FailedToGet { name: String, code: i32 },
    /// Failed to save item with error code.
    #[error("Failed to put keychain item '{name}' due to error {code}")]
    FailedToPut { name: String, code: i32 },
    /// Failed to update item with error code.
    #[error("Failed to update keychain item '{name}' due to error {code}")]
    FailedToUpdate { name: String, code: i32 },
    /// Failed to delete item with error code.
    #[error("Failed to delete keychain item '{name}' due to error {code}")]
    FailedToDelete { name: String, code: i32 },
}

impl From<Error> for KeychainError {
    fn from(error: Error) -> Self {
        KeychainError::App { error }
    }
}

impl From<KeychainError> for Error {
    fn from(value: KeychainError) -> Self {
        match value {
            KeychainError::App { error } => error,
            // If the error is not handled on the keychain error level,
            // then it's a logic error.
            keychain_error => Error::Fatal {
                error: keychain_error.to_string(),
            },
        }
    }
}

impl<T> From<std::sync::PoisonError<T>> for KeychainError {
    fn from(err: std::sync::PoisonError<T>) -> Self {
        Error::Fatal {
            error: err.to_string(),
        }
        .into()
    }
}

fn handle_not_found_for_if_exists(error: KeychainError) -> Result<(), KeychainError> {
    match error {
        KeychainError::NotFound { .. } => Ok(()),
        err => Err(err),
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use generic_array::{typenum::U32, GenericArray};

    use super::*;

    #[test]
    fn returns_same_key() -> Result<()> {
        let key = KeyMaterial::<U32>::random()?;
        let key_arr: GenericArray<u8, U32> = GenericArray::clone_from_slice(key.as_ref());
        let keychain = Keychain::new();
        keychain.upsert_local(KeyName::SkKeyEncryptionKey, key)?;
        let res = keychain.get_local::<U32>(KeyName::SkKeyEncryptionKey)?;
        let res_slice: &[u8] = res.as_ref();
        assert_eq!(res_slice, key_arr.as_slice());
        Ok(())
    }

    #[test]
    fn upsert_ok() -> Result<()> {
        let keychain = Keychain::new();
        let key_v1 = KeyMaterial::<U32>::random()?;
        keychain.upsert_local(KeyName::SkKeyEncryptionKey, key_v1)?;
        let key_v2 = KeyMaterial::<U32>::random()?;
        keychain.upsert_local(KeyName::SkKeyEncryptionKey, key_v2)?;
        Ok(())
    }

    #[test]
    fn delete_no_error_if_not_exists() -> Result<()> {
        let keychain = Keychain::new();
        let device_id: DeviceIdentifier = "device-id".to_string().try_into().unwrap();
        keychain.delete_synced_if_exists(&device_id, KeyName::SkKeyEncryptionKey)?;
        keychain.delete_local_if_exists(KeyName::SkKeyEncryptionKey)?;
        Ok(())
    }

    #[test]
    fn error_on_get_local_not_found() -> Result<()> {
        let keychain = Keychain::new();
        let res = keychain.get_local::<U32>(KeyName::SkKeyEncryptionKey);
        assert!(matches!(res, Err(KeychainError::NotFound { .. })));
        Ok(())
    }

    #[test]
    fn error_on_get_synced_not_found() -> Result<()> {
        let keychain = Keychain::new();
        let device_id: DeviceIdentifier = "device-id".to_string().try_into().unwrap();
        let res = keychain.get_synced::<U32>(&device_id, KeyName::SkKeyEncryptionKey);
        assert!(matches!(res, Err(KeychainError::NotFound { .. })));
        Ok(())
    }
}
