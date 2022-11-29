// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    collections::HashMap,
    fmt::{Debug, Formatter},
    sync::{Arc, RwLock},
};

use generic_array::ArrayLength;
use zeroize::Zeroizing;

use crate::{
    device::DeviceIdentifier,
    encryption::{
        key_material::KeyMaterial,
        keychains::keychain::{KeychainError, KeychainImpl},
        KeyName,
    },
};

type SyncedKey = (DeviceIdentifier, KeyName);

/// In-memory keychain for testing.
pub(super) struct InMemoryKeychain {
    local_data: Arc<RwLock<HashMap<KeyName, Zeroizing<Vec<u8>>>>>,
    synced_data: Arc<RwLock<HashMap<SyncedKey, Zeroizing<Vec<u8>>>>>,
}

impl InMemoryKeychain {
    pub fn new() -> Self {
        InMemoryKeychain {
            local_data: Arc::new(RwLock::new(HashMap::new())),
            synced_data: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl KeychainImpl for InMemoryKeychain {
    fn get_local<N: ArrayLength<u8>>(
        &self,
        name: KeyName,
    ) -> Result<KeyMaterial<N>, KeychainError> {
        let d = self.local_data.read()?;
        let key = d
            .get(&name)
            .ok_or_else(|| KeychainError::NotFound { name: name.into() })?;
        let km = KeyMaterial::<N>::from_slice(key.as_slice())?;
        Ok(km)
    }

    fn get_synced<N: ArrayLength<u8>>(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
    ) -> Result<KeyMaterial<N>, KeychainError> {
        let d = self.synced_data.read()?;
        let entry_name = synced_entry_name(device_identifier, name);
        let key = d
            .get(&entry_name)
            .ok_or_else(|| KeychainError::NotFound { name: name.into() })?;
        let km = KeyMaterial::<N>::from_slice(key.as_slice())?;
        Ok(km)
    }

    fn delete_local(&self, name: KeyName) -> Result<(), KeychainError> {
        let mut d = self.local_data.write()?;
        let _ = d.remove(&name);
        Ok(())
    }

    fn delete_synced(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
    ) -> Result<(), KeychainError> {
        let mut d = self.synced_data.write()?;
        let entry_name = synced_entry_name(device_identifier, name);
        let _ = d.remove(&entry_name);
        Ok(())
    }

    fn upsert_local<N: ArrayLength<u8>>(
        &self,
        name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), KeychainError> {
        let mut d = self.local_data.write()?;
        d.insert(name, key_to_vec(key));
        Ok(())
    }

    fn upsert_synced<N: ArrayLength<u8>>(
        &self,
        device_identifier: &DeviceIdentifier,
        name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), KeychainError> {
        let mut d = self.synced_data.write()?;
        let entry_name = synced_entry_name(device_identifier, name);
        d.insert(entry_name, key_to_vec(key));
        Ok(())
    }
}

fn key_to_vec<N: ArrayLength<u8>>(key: KeyMaterial<N>) -> Zeroizing<Vec<u8>> {
    let mut vec: Zeroizing<Vec<u8>> = Zeroizing::new(vec![0; key.len()]);
    vec.copy_from_slice(key.as_ref());
    vec
}

fn synced_entry_name(
    device_identifier: &DeviceIdentifier,
    name: KeyName,
) -> (DeviceIdentifier, KeyName) {
    (device_identifier.clone(), name)
}

impl Debug for InMemoryKeychain {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InMemoryKeychain").finish()
    }
}

impl From<(DeviceIdentifier, KeyName)> for KeyName {
    fn from(value: (DeviceIdentifier, KeyName)) -> Self {
        value.1
    }
}
