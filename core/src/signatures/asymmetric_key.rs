// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::encryption::DataEncryptionKey;
use crate::encryption::EncryptionOutput;
use crate::signatures::elliptic_curve::EllipticCurve;
use crate::Error;
// Must depend on k256 instead of elliptic_curve, because there are dependency resolution conflicts
// when specificying elliptic_curve as dependency directly.

use k256::elliptic_curve::{
    sec1::{FromEncodedPoint, ModulusSize, ToEncodedPoint, ValidatePublicKey},
    AffinePoint, Curve, FieldSize, ProjectiveArithmetic, PublicKey, SecretKey,
};
use k256::pkcs8::{AssociatedOid, EncodePublicKey};
use rand::thread_rng;
use std::fmt::{Debug, Formatter};

/// Elliptic curve key pair
#[derive(PartialEq, Eq)]
#[readonly::make]
pub struct AsymmetricKey<C>
where
    C: Curve + ProjectiveArithmetic + ValidatePublicKey,
    AffinePoint<C>: FromEncodedPoint<C> + ToEncodedPoint<C>,
    FieldSize<C>: ModulusSize,
{
    // `SecretKey` zeroizes on drop. We wrap it in a box to avoid leaving copies in memory when
    // `Self` is moved around and drop isn't called. This is not bullet proof unfortunately, because
    // copying moves can still happen when the secret key is constructed.
    pub(super) secret_key: Box<SecretKey<C>>,
    pub public_key: PublicKey<C>,
    pub curve: EllipticCurve,
}

impl<C> AsymmetricKey<C>
where
    C: Curve + ProjectiveArithmetic + ValidatePublicKey + AssociatedOid,
    AffinePoint<C>: FromEncodedPoint<C> + ToEncodedPoint<C>,
    FieldSize<C>: ModulusSize,
{
    pub(super) fn new(secret_key: Box<SecretKey<C>>) -> Result<Self, Error> {
        let public_key = secret_key.public_key();
        let curve = EllipticCurve::try_from(C::OID)?;
        Ok(Self {
            secret_key,
            public_key,
            curve,
        })
    }

    pub fn random() -> Result<AsymmetricKey<C>, Error> {
        // TODO the compiler could allocate `SecretKey` on the stack before moving it into the `Box`
        // which would leave a copy on the stack that won't be zeroized. Box::pin wouldn't help
        // here, because because the `SecretKey` would be still created on the stack first before
        // moving it in the box.
        // Also, we should be using the fallible RNG interface.
        let secret_key = Box::new(SecretKey::random(thread_rng()));
        Self::new(secret_key)
    }

    pub fn public_key_der(&self) -> Result<Vec<u8>, Error> {
        let der = self.public_key.to_public_key_der()?;
        Ok(der.as_bytes().into())
    }

    pub fn from_encrypted_der(
        encrypted_der: &EncryptionOutput,
        // Asymmetric keys are considered data in the key hierarchy (see data section in design for
        // more)
        key: &DataEncryptionKey,
    ) -> Result<Self, Error> {
        let der = key.decrypt_secret(encrypted_der)?;
        let secret_key = Box::new(SecretKey::from_sec1_der(&der)?);
        Self::new(secret_key)
    }

    pub fn to_encrypted_der(
        &self,
        key: &DataEncryptionKey,
    ) -> Result<EncryptionOutput, Error> {
        let der = self.secret_key.to_sec1_der()?;
        key.encrypt_secret(&der)
    }
}

impl<C> Debug for AsymmetricKey<C>
where
    C: Curve + ProjectiveArithmetic + ValidatePublicKey + AssociatedOid,
    AffinePoint<C>: FromEncodedPoint<C> + ToEncodedPoint<C>,
    FieldSize<C>: ModulusSize,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AsymmetricKey")
            .field("curve", &self.curve)
            .field("public_key", &self.public_key)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use anyhow::Result;
    use k256::Secp256k1;

    #[test]
    fn encrypt_decrypt() -> Result<()> {
        let dek = DataEncryptionKey::random("sk-dek".into())?;
        let kp: AsymmetricKey<Secp256k1> = AsymmetricKey::random()?;
        let encrypted_der = kp.to_encrypted_der(&dek)?;
        let decrypted: AsymmetricKey<Secp256k1> =
            AsymmetricKey::from_encrypted_der(&encrypted_der, &dek)?;

        assert_eq!(kp, decrypted);

        Ok(())
    }
}
