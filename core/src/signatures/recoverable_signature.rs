// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use ecdsa::{PrimeCurve, RecoveryId, Signature, SignatureSize};
use generic_array::ArrayLength;

#[derive(Clone, Debug)]
#[readonly::make]
pub struct RecoverableSignature<C>
where
    C: PrimeCurve,
    SignatureSize<C>: ArrayLength<u8>,
{
    pub signature: Signature<C>,
    pub recovery_id: RecoveryId,
}

impl<C> RecoverableSignature<C>
where
    C: PrimeCurve,
    SignatureSize<C>: ArrayLength<u8>,
{
    pub fn new(signature: Signature<C>, recovery_id: RecoveryId) -> Self {
        Self {
            signature,
            recovery_id,
        }
    }
}
