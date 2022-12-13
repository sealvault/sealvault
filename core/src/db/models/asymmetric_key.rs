// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::{prelude::*, SqliteConnection};
use generic_array::{typenum::U1, GenericArray};
use k256::pkcs8::DecodePublicKey;
use typed_builder::TypedBuilder;

use crate::{
    db::{
        deterministic_id::{DeterministicId, EntityName},
        models as m,
        schema::asymmetric_keys,
    },
    encryption::EncryptionOutput,
    signatures::EllipticCurve,
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
pub struct AsymmetricKey {
    pub deterministic_id: String,
    pub profile_id: String,
    pub dek_id: String,
    pub elliptic_curve: EllipticCurve,
    pub public_key: Vec<u8>,
    pub encrypted_der: EncryptionOutput,
    pub is_profile_wallet: bool,
    pub dapp_id: Option<String>,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl AsymmetricKey {
    pub fn list_all(conn: &mut SqliteConnection) -> Result<Vec<Self>, Error> {
        Ok(asymmetric_keys::table.load::<Self>(conn)?)
    }

    pub fn fetch_eth_public_key(
        conn: &mut SqliteConnection,
        deterministic_id: &str,
    ) -> Result<k256::PublicKey, Error> {
        use asymmetric_keys::dsl as ak;

        let public_key: Vec<u8> = asymmetric_keys::table
            .filter(ak::deterministic_id.eq(deterministic_id))
            .filter(ak::elliptic_curve.eq(EllipticCurve::Secp256k1))
            .select(ak::public_key)
            .first(conn)?;

        let public_key = k256::PublicKey::from_public_key_der(&public_key)?;
        Ok(public_key)
    }

    /// Fetch the key id for a dapp.
    /// Assumes one dapp key per profile.
    pub fn fetch_id_for_dapp<'a>(
        conn: &mut SqliteConnection,
        params: &'a impl m::DappSessionParams<'a>,
    ) -> Result<String, Error> {
        use asymmetric_keys::dsl as ak;

        let deterministic_id = asymmetric_keys::table
            .filter(ak::profile_id.eq(params.profile_id()))
            .filter(ak::dapp_id.eq(Some(params.dapp_id())))
            .select(ak::deterministic_id)
            .first(conn)?;

        Ok(deterministic_id)
    }

    pub fn set_profile_id(
        &self,
        connection: &mut SqliteConnection,
        profile_id: &str,
    ) -> Result<(), Error> {
        use asymmetric_keys::dsl as ak;

        diesel::update(
            asymmetric_keys::table
                .filter(ak::deterministic_id.eq(&self.deterministic_id)),
        )
        .set(ak::profile_id.eq(profile_id))
        .execute(connection)?;

        Ok(())
    }
}

#[derive(TypedBuilder, Insertable)]
#[readonly::make]
#[diesel(table_name = asymmetric_keys)]
pub struct NewAsymmetricKey<'a> {
    #[builder(setter(into))]
    pub profile_id: &'a str,
    #[builder(setter(into))]
    pub dek_id: &'a str,
    #[builder(setter(into))]
    pub public_key: &'a [u8],
    pub elliptic_curve: EllipticCurve,
    pub encrypted_der: &'a EncryptionOutput,
    #[builder(default = false)]
    pub is_profile_wallet: bool,
    #[builder(default = None)]
    pub dapp_id: Option<&'a str>,
}

impl<'a> NewAsymmetricKey<'a> {
    /// Create a new asymmetric key and return its deterministic id.
    pub fn insert(&self, conn: &mut SqliteConnection) -> Result<String, Error> {
        use asymmetric_keys::dsl as ak;

        let deterministic_id = self.deterministic_id()?;
        let created_at = rfc3339_timestamp();

        diesel::insert_into(asymmetric_keys::table)
            .values((
                self,
                ak::deterministic_id.eq(&deterministic_id),
                ak::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(deterministic_id)
    }
}

impl<'a> DeterministicId<'a, &'a [u8], U1> for NewAsymmetricKey<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::AsymmetricKey
    }

    fn unique_columns(&'a self) -> GenericArray<&'a [u8], U1> {
        [self.public_key].into()
    }
}
