// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::encryption::key_material::KeyMaterial;
use crate::encryption::keychains::keychain::KeychainImpl;
use crate::Error;

use crate::encryption::KeyEncryptionKey;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::sync::{Arc, Mutex};

/// In-memory keychain for testing.
pub(super) struct InMemoryKeychain {
    data: Arc<Mutex<HashMap<String, KeyMaterial>>>,
}

impl InMemoryKeychain {
    pub fn new() -> Self {
        let data = Arc::new(Mutex::new(HashMap::new()));
        InMemoryKeychain { data }
    }
}

impl KeychainImpl for InMemoryKeychain {
    fn get(&self, name: &str) -> Result<KeyEncryptionKey, Error> {
        let d = self.data.lock()?;
        // Only case when we want to use the `clone_for_in_memory_keychain` method.
        #[allow(deprecated)]
        let key_material = d
            .get(name)
            .map(|s| (*s).clone_for_in_memory_keychain().expect("valid key"))
            .ok_or_else(|| Error::Fatal {
                error: format!("Key '{}' not found", name),
            })?;
        Ok(KeyEncryptionKey::new(name.into(), key_material))
    }

    fn put_local_unlocked(&self, key: KeyEncryptionKey) -> Result<(), Error> {
        let mut d = self.data.lock()?;
        let (name, key_material) = key.into_keychain();
        d.insert(name, key_material);
        Ok(())
    }
}

impl Debug for InMemoryKeychain {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InMemoryKeychain").finish()
    }
}
