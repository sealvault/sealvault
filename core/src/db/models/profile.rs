// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use diesel::{prelude::*, SqliteConnection};
use generic_array::{typenum::U1, GenericArray};
use typed_builder::TypedBuilder;

use crate::{
    db::{
        deterministic_id::{DeterministicId, EntityName},
        models as m,
        schema::profiles,
        DeferredTxConnection,
    },
    encryption::Keychain,
    protocols::eth,
    utils::{new_uuid, rfc3339_timestamp},
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable, Insertable)]
#[diesel(primary_key(deterministic_id))]
pub struct Profile {
    pub deterministic_id: String,
    pub uuid: String,
    pub name: String,
    pub picture_id: String,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl Profile {
    pub fn list_all(conn: &mut SqliteConnection) -> Result<Vec<Profile>, Error> {
        Ok(profiles::table.load::<Profile>(conn)?)
    }

    /// Create a new profile with Ethereum protocol wallet addresses and return the profile's
    /// deterministic id.
    pub fn create_eth_profile(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        params: &ProfileParams,
    ) -> Result<String, Error> {
        let picture_id = m::ProfilePicture::insert_bundled(
            tx_conn.as_mut(),
            params.bundled_picture_name,
        )?;
        let profile_id = Self::create(tx_conn.as_mut(), params.name, &picture_id)?;

        let create_params = m::CreateEthAddressParams::builder()
            .profile_id(&profile_id)
            .chain_id(eth::ChainId::default_wallet_chain())
            .is_profile_wallet(true)
            .build();
        let _ =
            m::Address::create_eth_key_and_address(tx_conn, keychain, &create_params)?;

        Ok(profile_id)
    }

    /// Create a new profile and return its deterministic id.
    fn create(
        conn: &mut SqliteConnection,
        name: &str,
        picture_id: &str,
    ) -> Result<String, Error> {
        use profiles::dsl as p;

        let uuid = new_uuid();
        let entity = ProfileEntity { uuid: &uuid };
        let deterministic_id = entity.deterministic_id()?;
        let created_at = rfc3339_timestamp();

        diesel::insert_into(profiles::table)
            .values((
                p::deterministic_id.eq(&deterministic_id),
                p::uuid.eq(&entity.uuid),
                p::name.eq(name),
                p::picture_id.eq(picture_id),
                p::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(deterministic_id)
    }

    pub fn delete(
        conn: &mut SqliteConnection,
        deterministic_id: &str,
    ) -> Result<(), Error> {
        use profiles::dsl as p;

        diesel::delete(profiles::table.filter(p::deterministic_id.eq(deterministic_id)))
            .execute(conn)?;

        Ok(())
    }

    pub fn insert(&self, conn: &mut SqliteConnection) -> Result<(), Error> {
        diesel::insert_into(profiles::table)
            .values(self)
            .execute(conn)?;
        Ok(())
    }

    pub fn set_picture_id(
        &self,
        conn: &mut SqliteConnection,
        picture_id: &str,
    ) -> Result<(), Error> {
        use profiles::dsl as p;

        diesel::update(
            profiles::table.filter(p::deterministic_id.eq(&self.deterministic_id)),
        )
        .set(p::picture_id.eq(picture_id))
        .execute(conn)?;

        Ok(())
    }

    /// Deprecated, because UUID should be stable. Only used in data migration to update temporary
    /// uuid.
    #[deprecated]
    pub fn set_uuid(&self, conn: &mut SqliteConnection, uuid: &str) -> Result<(), Error> {
        use profiles::dsl as p;

        diesel::update(
            profiles::table.filter(p::deterministic_id.eq(&self.deterministic_id)),
        )
        .set(p::uuid.eq(uuid))
        .execute(conn)?;

        Ok(())
    }
}

// Struct with typed builder ensures that arguments of same type aren't mixed up as Rust doesn't
// have named parameters.
#[derive(TypedBuilder)]
#[readonly::make]
pub struct ProfileParams<'a> {
    #[builder(setter(into))]
    name: &'a str,
    #[builder(setter(into))]
    bundled_picture_name: &'a str,
}

pub struct ProfileEntity<'a> {
    pub uuid: &'a str,
}

impl<'a> DeterministicId<'a, &'a str, U1> for ProfileEntity<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::Profile
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U1> {
        // When a user creates profiles on different devices those should be different entities,
        // hence the uuid as deterministic id. The name should be changeable without creating a new
        // entity.
        [self.uuid].into()
    }
}
