// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    default::Default,
    fmt::{Debug, Formatter},
};

use generic_array::{typenum::U32, ArrayLength, GenericArray};
use subtle::ConstantTimeEq;
use zeroize::Zeroize;

use crate::{utils::try_fill_random_bytes, Error};

const INVARIANT_VIOLATION: &str = "Invariant violation";

/// Encryption key material.
/// We store the key in a boxed array so that when the struct gets moved, no copies are made of the
/// key material. This would be a problem, because we couldn't zeroize those copies.
/// More info: https://archive.ph/CVSHe
pub(super) struct KeyMaterial<N: ArrayLength<u8>>(Box<GenericArray<u8, N>>);

impl<N: ArrayLength<u8>> KeyMaterial<N> {
    // Not used on all targets
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

// Auto-deriving ZeroizeOnDrop doesn't work due to the generic param.
impl<N: ArrayLength<u8>> Zeroize for KeyMaterial<N> {
    fn zeroize(&mut self) {
        self.0.zeroize()
    }
}

impl<N: ArrayLength<u8>> Drop for KeyMaterial<N> {
    fn drop(&mut self) {
        self.zeroize();
    }
}

impl<N: ArrayLength<u8>> KeyMaterial<N> {
    pub(super) fn new(buffer: Box<GenericArray<u8, N>>) -> Result<Self, Error> {
        let default: GenericArray<u8, N> = Default::default();
        if buffer.ct_eq(&default).unwrap_u8() == 1 {
            return Err(Error::Fatal {
                error: INVARIANT_VIOLATION.into(),
            });
        }
        Ok(Self(buffer))
    }

    pub(super) fn random() -> Result<Self, Error> {
        let mut buffer: Box<GenericArray<u8, N>> = Box::default();
        try_fill_random_bytes(&mut buffer)?;
        Self::new(buffer)
    }

    pub(super) fn from_slice(bytes: &[u8]) -> Result<Self, Error> {
        let mut buffer: Box<GenericArray<u8, N>> = Box::default();
        if buffer.len() != bytes.len() {
            return Err(Error::Fatal {
                error: INVARIANT_VIOLATION.into(),
            });
        }
        buffer.copy_from_slice(bytes);
        Self::new(buffer)
    }
}

impl<N: ArrayLength<u8>> Debug for KeyMaterial<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let len = self.0.len();
        let s = format!("KeyMaterial(length: {len})");
        f.debug_struct(&s).finish()
    }
}

impl<N: ArrayLength<u8>> Clone for KeyMaterial<N> {
    fn clone(&self) -> Self {
        Self::from_slice(self.0.as_slice())
            .expect("invariants are already checked in `self`")
    }
}

impl<N: ArrayLength<u8>> AsRef<[u8]> for KeyMaterial<N> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

impl AsRef<chacha20poly1305::Key> for KeyMaterial<U32> {
    fn as_ref(&self) -> &chacha20poly1305::Key {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;

    #[test]
    fn fatal_error_on_default() {
        let key_array: GenericArray<u8, U32> = Default::default();
        let res = KeyMaterial::new(Box::new(key_array));
        assert!(matches!(res, Err(Error::Fatal { error: _ })));
    }

    #[test]
    fn fatal_error_on_length_mismatch() {
        let mut array = vec![0_u8; 16];
        try_fill_random_bytes(&mut array).expect("random fail");
        let res = KeyMaterial::<U32>::from_slice(&array);
        assert!(matches!(res, Err(Error::Fatal { error: _ })));
    }

    #[test]
    fn zeroizes() -> Result<()> {
        let bytes = 32;
        let mut key = KeyMaterial::<U32>::random()?;
        let ptr = key.0.as_ptr();
        key.zeroize();
        let default: GenericArray<u8, U32> = Default::default();
        let slice: &[u8] = default.as_slice();
        unsafe {
            assert_eq!(core::slice::from_raw_parts(ptr, bytes), slice);
        }
        Ok(())
    }
}
