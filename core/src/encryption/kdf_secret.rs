// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use generic_array::typenum::U32;

use crate::{
    device::DeviceIdentifier,
    encryption::{key_material::KeyMaterial, KeyName, Keychain},
    Error,
};

pub struct KdfSecret(KeyMaterial<U32>);

const NAME: KeyName = KeyName::KdfSecret;

impl KdfSecret {
    pub fn setup_or_rotate(
        keychain: &Keychain,
        device_identifier: &DeviceIdentifier,
    ) -> Result<Self, Error> {
        let kdf_secret = Self::random()?;
        kdf_secret.save_to_keychain(keychain, device_identifier)?;
        Self::from_keychain(keychain, device_identifier)
    }

    fn random() -> Result<Self, Error> {
        Ok(Self(KeyMaterial::<U32>::random()?))
    }

    pub fn from_keychain(
        keychain: &Keychain,
        device_identifier: &DeviceIdentifier,
    ) -> Result<Self, Error> {
        let key_material = keychain.get_synced(device_identifier, NAME)?;
        Ok(KdfSecret(key_material))
    }

    pub fn save_to_keychain(
        self,
        keychain: &Keychain,
        device_identifier: &DeviceIdentifier,
    ) -> Result<(), Error> {
        keychain.upsert_synced(device_identifier, NAME, self.0)?;
        Ok(())
    }

    pub fn delete_from_keychain_if_exists(
        keychain: &Keychain,
        device_identifier: &DeviceIdentifier,
    ) -> Result<(), Error> {
        keychain.delete_synced_if_exists(device_identifier, NAME)?;
        Ok(())
    }

    pub(super) fn expose_secret(&self) -> &[u8] {
        self.0.as_ref()
    }
}
