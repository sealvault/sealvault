// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::str::FromStr;

use generic_array::{typenum::U16, GenericArray};

use crate::{utils::try_random_bytes, Error};

pub struct KdfNonce(GenericArray<u8, U16>);

impl KdfNonce {
    pub fn random() -> Result<Self, Error> {
        let kdf_nonce: GenericArray<u8, U16> = try_random_bytes()?;
        Ok(Self(kdf_nonce))
    }
}

impl AsRef<[u8]> for KdfNonce {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl TryFrom<Vec<u8>> for KdfNonce {
    type Error = Error;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        let arr: [u8; 16] = value.try_into().map_err(|_| Error::Fatal {
            error: "Failed to convert value to kdf nonce".into(),
        })?;

        Ok(KdfNonce(GenericArray::from(arr)))
    }
}

impl FromStr for KdfNonce {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let buffer = base64::decode(s)?;
        buffer.try_into()
    }
}
