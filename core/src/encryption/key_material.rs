// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::utils::try_fill_random_bytes;
use crate::Error;
use std::default::Default;
use std::fmt::{Debug, Formatter};
use subtle::ConstantTimeEq;

use zeroize::ZeroizeOnDrop;

const KEY_BYTES: usize = 32;
pub type KeyArray = [u8; KEY_BYTES];

/// Encryption key material.
/// We store the key in a boxed array so that when the struct gets moved, no copies are made of the
/// key material. This would be a problem, because we couldn't zeroize those copies.
/// More info: https://archive.ph/CVSHe
#[derive(ZeroizeOnDrop)]
pub(super) struct KeyMaterial(Box<KeyArray>);

impl KeyMaterial {
    pub(super) fn new(buffer: Box<KeyArray>) -> Result<Self, Error> {
        let default: KeyArray = Default::default();
        if buffer.ct_eq(&default).unwrap_u8() == 1 {
            return Err(Error::Fatal {
                error: "Invariant violation".into(),
            });
        }
        Ok(Self(buffer))
    }

    pub(super) fn random() -> Result<Self, Error> {
        let mut buffer: Box<KeyArray> = Box::new(Default::default());
        try_fill_random_bytes(&mut *buffer)?;
        Self::new(buffer)
    }

    pub(super) fn from_slice(bytes: &[u8]) -> Result<Self, Error> {
        if KEY_BYTES.ct_eq(&bytes.len()).unwrap_u8() == 0 {
            return Err(Error::Fatal {
                error: "Invariant violation".into(),
            });
        }
        let mut buffer: Box<KeyArray> = Box::new(Default::default());
        buffer.copy_from_slice(bytes);
        Self::new(buffer)
    }

    /// We don't want to provide `Clone` for the `KeyMaterial`, as it's only needed for the
    /// in-memory key chain which is only used during development and testing.
    /// Cloning the vector should allocate the necessary memory upfront, so there wouldn't be
    /// unreachable copies for zeroization, but it's implementation dependent, so it's best to not
    /// take chances.
    /// We restrict this methods visibility, mark it as deprecated, and only implement it for debug
    /// targets to prevent its usage for cases other than the in-memory keychain.re won't be
    #[cfg(debug_assertions)]
    #[deprecated]
    #[allow(dead_code)]
    pub(super) fn clone_for_in_memory_keychain(&self) -> Result<Self, Error> {
        Self::from_slice(self.0.as_slice())
    }
}

impl Debug for KeyMaterial {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KeyMaterial").finish()
    }
}

impl AsRef<[u8]> for KeyMaterial {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

impl AsRef<chacha20poly1305::Key> for KeyMaterial {
    fn as_ref(&self) -> &chacha20poly1305::Key {
        self.0.as_slice().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fatal_error_on_default() {
        let key_array: KeyArray = Default::default();
        let res = KeyMaterial::new(Box::new(key_array));
        assert!(matches!(res, Err(Error::Fatal { error: _ })));
    }

    #[test]
    fn fatal_error_on_length_mismatch() {
        let mut array = vec![0_u8; 16];
        try_fill_random_bytes(&mut array).expect("random fail");
        let res = KeyMaterial::from_slice(&array);
        assert!(matches!(res, Err(Error::Fatal { error: _ })));
    }
}
