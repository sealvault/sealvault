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
    encryption::{key_material::KeyMaterial, keychains::keychain::KeychainImpl, KeyName},
    Error,
};

/// In-memory keychain for testing.
pub(super) struct InMemoryKeychain {
    data: Arc<RwLock<HashMap<KeyName, Zeroizing<Vec<u8>>>>>,
}

impl InMemoryKeychain {
    pub fn new() -> Self {
        let data = Arc::new(RwLock::new(HashMap::new()));
        InMemoryKeychain { data }
    }
}

impl KeychainImpl for InMemoryKeychain {
    fn get<N: ArrayLength<u8>>(&self, name: KeyName) -> Result<KeyMaterial<N>, Error> {
        let d = self.data.read()?;
        let key = d.get(&name).ok_or_else(|| Error::Fatal {
            error: format!("Key '{name}' not found"),
        })?;
        KeyMaterial::<N>::from_slice(key.as_slice())
    }

    fn delete_local(&self, name: KeyName) -> Result<(), Error> {
        let mut d = self.data.write()?;
        let _ = d.remove(&name);
        Ok(())
    }

    fn put_local<N: ArrayLength<u8>>(
        &self,
        name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), Error> {
        use std::collections::hash_map::Entry;
        let mut d = self.data.write()?;
        if let Entry::Vacant(e) = d.entry(name) {
            let mut vec: Zeroizing<Vec<u8>> = Zeroizing::new(vec![0; key.len()]);
            vec.copy_from_slice(key.as_ref());
            e.insert(vec);
            Ok(())
        } else {
            Err(Error::Fatal {
                error: "A keychain item by this name already exists".into(),
            })
        }
    }
}

impl Debug for InMemoryKeychain {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InMemoryKeychain").finish()
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
        let imk = InMemoryKeychain::new();
        imk.put_local(KeyName::SkKeyEncryptionKey, key)?;
        let res = imk.get::<U32>(KeyName::SkKeyEncryptionKey)?;
        let res_slice: &[u8] = res.as_ref();
        assert_eq!(res_slice, key_arr.as_slice());
        Ok(())
    }

    #[test]
    fn error_on_same_name_twice() -> Result<()> {
        let imk = InMemoryKeychain::new();
        let key = KeyMaterial::<U32>::random()?;
        imk.put_local(KeyName::SkKeyEncryptionKey, key)?;
        let key = KeyMaterial::<U32>::random()?;
        let res = imk.put_local(KeyName::SkKeyEncryptionKey, key);
        assert!(res.is_err());
        Ok(())
    }

    #[test]
    fn error_on_not_found() -> Result<()> {
        let imk = InMemoryKeychain::new();
        let res = imk.get::<U32>(KeyName::SkKeyEncryptionKey);
        assert!(res.is_err());
        Ok(())
    }
}
