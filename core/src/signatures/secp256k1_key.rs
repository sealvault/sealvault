// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use k256::{
    ecdsa::{
        recoverable::Signature as RecoverableSignature, signature::DigestSigner,
        SigningKey,
    },
    Secp256k1,
};
use sha3::Keccak256;

use crate::{signatures::AsymmetricKey, Error};

impl AsymmetricKey<Secp256k1> {
    /// Perform an ECDSA signature on a Keccak256 pre-hashed message using the Secp256k1 curve with
    /// RFC6979 deterministic `k` value.
    pub fn try_sign_digest(
        &self,
        digest: Keccak256,
    ) -> Result<RecoverableSignature, Error> {
        let signing_key: SigningKey = (&*self.secret_key).into();
        let sig = signing_key.try_sign_digest(digest)?;
        Ok(sig)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use k256::{
        ecdsa::{signature::Verifier, VerifyingKey},
        PublicKey,
    };
    use sha3::{Digest, Keccak256};

    use super::*;

    // Only parsing keys in tests.
    impl std::str::FromStr for AsymmetricKey<Secp256k1> {
        type Err = anyhow::Error;

        fn from_str(src: &str) -> Result<Self, Self::Err> {
            let src = hex::decode(src)?;
            let sk = Box::new(k256::SecretKey::from_be_bytes(&src)?);
            Ok(Self::new(sk)?)
        }
    }

    #[test]
    fn sign_verify() -> Result<()> {
        let key: AsymmetricKey<Secp256k1> = AsymmetricKey::random()?;
        let message = "hello world";
        let digest = Keccak256::new_with_prefix(message);
        let signature: RecoverableSignature = key.try_sign_digest(digest)?;

        let verifying_key: VerifyingKey = key.public_key.into();
        verifying_key.verify(message.as_bytes(), &signature)?;

        let recovered_key: VerifyingKey =
            signature.recover_verifying_key(message.as_ref())?;
        assert_eq!(verifying_key, recovered_key);
        let recovered_pk: PublicKey = PublicKey::from(recovered_key);
        assert_eq!(recovered_pk, key.public_key);

        Ok(())
    }
}
