// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

#[cfg(not(target_os = "ios"))]
use crate::encryption::keychains::in_memory_keychain::InMemoryKeychain;
#[cfg(target_os = "ios")]
use crate::encryption::keychains::ios_keychain::IOSKeychain;
use crate::{
    config, encryption::encryption_key::KeyEncryptionKey, utils::unix_timestamp, Error,
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
    fn get(&self, name: &str) -> Result<KeyEncryptionKey, Error>;

    fn soft_delete(&self, name: &str) -> Result<(), Error>;

    /// Put an item on the local keychain that is only available when the device is unlocked.
    /// The item will NOT be synced.
    fn put_local_unlocked(&self, key: KeyEncryptionKey) -> Result<(), Error>;
}

pub(super) fn soft_delete_rename(name: &str) -> String {
    format!("{}-DELETED-{}", name, unix_timestamp())
}

#[derive(Debug)]
pub struct Keychain {
    keychain: Box<dyn KeychainImpl>,
}

impl Keychain {
    #[cfg(target_os = "ios")]
    pub fn new() -> Self {
        let keychain = Box::new(IOSKeychain::new());
        Self { keychain }
    }

    #[cfg(not(target_os = "ios"))]
    pub fn new() -> Self {
        let keychain = Box::new(InMemoryKeychain::new());
        Self { keychain }
    }

    /// Get a symmetric key from the keychain.
    pub fn get_sk_kek(&self) -> Result<KeyEncryptionKey, Error> {
        self.keychain.get(config::SK_KEK_NAME)
    }

    pub fn soft_delete_sk_kek(&self) -> Result<(), Error> {
        self.keychain.soft_delete(config::SK_KEK_NAME)
    }

    /// Store a symmetric key on the local keychain encoded that is available when the device is
    /// unlocked.
    pub fn put_local_unlocked(&self, key: KeyEncryptionKey) -> Result<(), Error> {
        self.keychain.put_local_unlocked(key)
    }
}

impl Default for Keychain {
    fn default() -> Self {
        Self::new()
    }
}
