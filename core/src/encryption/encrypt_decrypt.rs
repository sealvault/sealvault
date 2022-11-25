// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use aead::{Aead, NewAead, Payload};
use chacha20poly1305::{XChaCha20Poly1305, XNonce};

use crate::{
    encryption::{
        encryption_key::ExposeKeyMaterial, encryption_output::EncryptionOutput,
    },
    utils, Error,
};

pub(super) fn encrypt<'msg, 'aad, 'key>(
    plaintext: impl Into<Payload<'msg, 'aad>>,
    key: &'key impl ExposeKeyMaterial<'key>,
) -> Result<EncryptionOutput, Error> {
    let nonce: XNonce = utils::try_random_bytes()?;
    // The cipher will make a copy of the reference, but the library takes care of zeroizing the
    // copy properly.
    let cipher = XChaCha20Poly1305::new(key.expose_secret().as_ref());
    let cipher_text = cipher.encrypt(&nonce, plaintext)?;
    Ok(EncryptionOutput::builder()
        .nonce(nonce)
        .cipher_text(cipher_text)
        .build())
}

pub(super) fn decrypt<'msg, 'aad, 'key>(
    ciphertext: impl Into<Payload<'msg, 'aad>>,
    key: &'key impl ExposeKeyMaterial<'key>,
    nonce: &XNonce,
) -> Result<Vec<u8>, Error> {
    let cipher = XChaCha20Poly1305::new(key.expose_secret().as_ref());
    let plain_text = cipher.decrypt(nonce, ciphertext)?;
    Ok(plain_text)
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;
    use crate::encryption::{encryption_key::DataEncryptionKey, KeyName};

    #[test]
    fn encrypt_decrypt() -> Result<()> {
        let key = DataEncryptionKey::random(KeyName::SkDataEncryptionKey)?;
        let message = b"hello-world";
        let aad = b"aad";
        let encryption_payload = Payload { msg: message, aad };
        let encryption_output = encrypt(encryption_payload, &key)?;

        let decryption_payload = Payload {
            msg: &encryption_output.cipher_text,
            aad,
        };
        let decrypted = decrypt(decryption_payload, &key, &encryption_output.nonce)?;

        assert_eq!(decrypted, message);

        Ok(())
    }
}
