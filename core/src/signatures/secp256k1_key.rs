// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use k256::{ecdsa::SigningKey, Secp256k1};
use sha3::Keccak256;

use crate::{
    signatures::{recoverable_signature::RecoverableSignature, AsymmetricKey},
    Error,
};

impl AsymmetricKey<Secp256k1> {
    /// Perform an ECDSA signature on a Keccak256 pre-hashed message using the Secp256k1 curve with
    /// RFC6979 deterministic `k` value.
    pub fn try_sign_digest(
        &self,
        digest: Keccak256,
    ) -> Result<RecoverableSignature<Secp256k1>, Error> {
        let signing_key: SigningKey = (&*self.secret_key).into();
        let (signature, recovery_id) = signing_key.sign_digest_recoverable(digest)?;
        Ok(RecoverableSignature::new(signature, recovery_id))
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use k256::{
        ecdsa::{signature::DigestVerifier, VerifyingKey},
        FieldBytes, PublicKey,
    };
    use sha3::{Digest, Keccak256};

    use super::*;

    // Only parsing keys in tests.
    impl std::str::FromStr for AsymmetricKey<Secp256k1> {
        type Err = anyhow::Error;

        fn from_str(src: &str) -> Result<Self, Self::Err> {
            let src = hex::decode(src)?;
            let src = FieldBytes::from_exact_iter(src.into_iter()).ok_or_else(|| {
                Error::Fatal {
                    error: "Invalid key length".into(),
                }
            })?;
            let sk = Box::new(k256::SecretKey::from_bytes(&src)?);
            Ok(Self::new(sk)?)
        }
    }

    #[test]
    fn sign_verify() -> Result<()> {
        let key: AsymmetricKey<Secp256k1> = AsymmetricKey::random()?;
        let message = "hello world";
        let digest = Keccak256::new_with_prefix(message);
        let sig = key.try_sign_digest(digest)?;

        let verifying_key: VerifyingKey = key.public_key.into();
        let digest = Keccak256::new_with_prefix(message);
        verifying_key.verify_digest(digest, &sig.signature)?;

        let digest = Keccak256::new_with_prefix(message);
        let recovered_key =
            VerifyingKey::recover_from_digest(digest, &sig.signature, sig.recovery_id)?;
        let digest = Keccak256::new_with_prefix(message);
        recovered_key.verify_digest(digest, &sig.signature)?;

        assert_eq!(verifying_key, recovered_key);
        let recovered_pk: PublicKey = PublicKey::from(recovered_key);
        assert_eq!(recovered_pk, key.public_key);

        Ok(())
    }
}
