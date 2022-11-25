// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use generic_array::typenum::U32;

use crate::{
    encryption::{key_material::KeyMaterial, KeyName, Keychain},
    Error,
};

pub struct KdfSecret(KeyMaterial<U32>);

impl KdfSecret {
    pub fn setup(keychain: &Keychain) -> Result<Self, Error> {
        let kdf_secret = Self::random()?;
        kdf_secret.save_to_synced_keychain(keychain)?;
        Self::from_keychain(keychain)
    }

    pub(super) fn random() -> Result<Self, Error> {
        let key = KeyMaterial::<U32>::random()?;
        Ok(KdfSecret(key))
    }

    pub fn from_keychain(keychain: &Keychain) -> Result<Self, Error> {
        let key_material = keychain.get(KeyName::KdfSecret)?;
        Ok(KdfSecret(key_material))
    }

    fn save_to_synced_keychain(self, keychain: &Keychain) -> Result<(), Error> {
        keychain.put_synced(KeyName::KdfSecret, self.0)
    }

    pub(super) fn expose_secret(&self) -> &[u8] {
        self.0.as_ref()
    }
}
