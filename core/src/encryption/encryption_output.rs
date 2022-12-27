// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter};

use chacha20poly1305::XNonce;
use diesel::{deserialize::FromSql, serialize::ToSql, sql_types::Binary, sqlite::Sqlite};
use typed_builder::TypedBuilder;

use crate::Error;

const NONCE_BYTES: usize = 24;
const TAG_BYTES: usize = 16;

#[derive(Clone, PartialEq, Eq, TypedBuilder, AsExpression, FromSqlRow)]
#[diesel(sql_type = Binary)]
#[readonly::make]
pub struct EncryptionOutput {
    #[builder(setter(into))]
    pub cipher_text: Vec<u8>,
    #[builder(setter(into))]
    pub nonce: XNonce,
}

impl Debug for EncryptionOutput {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EncryptionOutput").finish()
    }
}

impl From<&EncryptionOutput> for Vec<u8> {
    fn from(encryption_output: &EncryptionOutput) -> Self {
        let length = NONCE_BYTES + encryption_output.cipher_text.len();
        let mut v: Vec<u8> = Vec::with_capacity(length);
        v.extend(encryption_output.nonce.into_iter());
        v.extend(encryption_output.cipher_text.clone().into_iter());
        v
    }
}

fn vector_too_short_error() -> Error {
    Error::Fatal {
        error: "Vector is too short.".into(),
    }
}

impl TryFrom<Vec<u8>> for EncryptionOutput {
    type Error = Error;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        let mut slice = value.as_slice();
        let nonce = slice
            .take(..NONCE_BYTES)
            .ok_or_else(vector_too_short_error)?;
        let nonce: [u8; NONCE_BYTES] =
            nonce.try_into().map_err(|_| vector_too_short_error())?;
        if slice.len() < TAG_BYTES + 1 {
            return Err(vector_too_short_error());
        }
        let out = EncryptionOutput::builder()
            .cipher_text(slice)
            .nonce(nonce)
            .build();
        Ok(out)
    }
}

impl FromSql<Binary, Sqlite> for EncryptionOutput {
    fn from_sql(
        bytes: diesel::backend::RawValue<Sqlite>,
    ) -> diesel::deserialize::Result<Self> {
        let v = <Vec<u8> as FromSql<Binary, Sqlite>>::from_sql(bytes)?;
        v.try_into().map_err(|err: Error| {
            let e: Box<dyn std::error::Error + Send + Sync> = Box::new(err);
            e
        })
    }
}

impl ToSql<Binary, Sqlite> for EncryptionOutput {
    fn to_sql(
        &self,
        out: &mut diesel::serialize::Output<Sqlite>,
    ) -> diesel::serialize::Result {
        let v: Vec<u8> = self.into();
        out.set_value(v);
        Ok(diesel::serialize::IsNull::No)
    }
}

#[cfg(test)]
mod tests {
    use aead::Payload;
    use anyhow::Result;

    use super::*;
    use crate::encryption::{
        encrypt_decrypt::{decrypt, encrypt},
        DataEncryptionKey, KeyName,
    };

    #[test]
    fn to_vec_from_vec() -> Result<()> {
        let key = DataEncryptionKey::random(KeyName::SkDataEncryptionKey)?;
        let msg = b"message";
        let aad = b"aad";
        let encryption_payload = Payload { msg, aad };
        let encryption_output = encrypt(encryption_payload, &key)?;
        let encryption_output_vec: Vec<u8> = (&encryption_output).into();
        let encryption_output: EncryptionOutput =
            encryption_output_vec.try_into().unwrap();

        let decryption_payload = Payload {
            msg: &encryption_output.cipher_text,
            aad,
        };
        let decrypted = decrypt(decryption_payload, &key, &encryption_output.nonce)?;

        assert_eq!(decrypted, msg);

        Ok(())
    }

    #[test]
    fn no_panic_on_short_from_vec() -> Result<()> {
        let v: Vec<u8> = vec![1, 2];
        let result: Result<EncryptionOutput, Error> = TryFrom::<Vec<u8>>::try_from(v);
        assert!(format!("{:?}", result).to_lowercase().contains("short"));

        Ok(())
    }
}
