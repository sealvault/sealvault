// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{fmt::Debug, str::FromStr};

use derive_more::{AsRef, Display, Into};
use diesel::{prelude::*, SqliteConnection};
use generic_array::{typenum::U1, GenericArray};
use serde::{Deserialize, Serialize};

use crate::{
    config,
    db::{
        deterministic_id::{DeriveDeterministicId, EntityName},
        models as m,
        schema::profiles,
        DeferredTxConnection, DeterministicId,
    },
    encryption::Keychain,
    protocols::eth,
    utils::{new_uuid, rfc3339_timestamp},
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable, Insertable)]
#[diesel(primary_key(deterministic_id))]
pub struct Profile {
    pub deterministic_id: DeterministicId,
    pub uuid: String,
    pub name: String,
    pub picture_id: DeterministicId,
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
        name: &ProfileName,
        bundled_picture_name: &str,
    ) -> Result<DeterministicId, Error> {
        let picture_id =
            m::ProfilePicture::insert_bundled(tx_conn.as_mut(), bundled_picture_name)?;
        let profile_id = Self::create(tx_conn.as_mut(), name, &picture_id)?;

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
        name: &ProfileName,
        picture_id: &DeterministicId,
    ) -> Result<DeterministicId, Error> {
        use profiles::dsl as p;

        let uuid = new_uuid();
        let entity = ProfileEntity { uuid: &uuid };
        let deterministic_id = entity.deterministic_id()?;
        let created_at = rfc3339_timestamp();

        diesel::insert_into(profiles::table)
            .values((
                p::deterministic_id.eq(&deterministic_id),
                p::uuid.eq(&entity.uuid),
                p::name.eq(name.as_ref()),
                p::picture_id.eq(picture_id),
                p::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(deterministic_id)
    }

    pub fn delete(
        conn: &mut SqliteConnection,
        deterministic_id: &DeterministicId,
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
        picture_id: &DeterministicId,
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

/// The device name that let's the user identifies the device.
#[derive(
    Debug, Display, Clone, Eq, PartialEq, Hash, Into, AsRef, Serialize, Deserialize,
)]
#[serde(try_from = "String")]
#[serde(into = "String")]
#[repr(transparent)]
pub struct ProfileName(String);

impl TryFrom<String> for ProfileName {
    type Error = Error;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Err(Error::User {
                explanation: "Profile name must not be empty".into(),
            })
        // String in length in Rust returns number of bytes, but we want to check number of chars
        // due to unicode.
        } else if value.chars().count() > config::MAX_PROFILE_NAME_LENGTH {
            Err(Error::User {
                explanation: format!(
                    "Profile name too long. Please limit to {} characters",
                    config::MAX_PROFILE_NAME_LENGTH
                ),
            })
        } else {
            Ok(Self(value))
        }
    }
}

impl FromStr for ProfileName {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.to_string().try_into()
    }
}

pub struct ProfileEntity<'a> {
    pub uuid: &'a str,
}

impl<'a> DeriveDeterministicId<'a, &'a str, U1> for ProfileEntity<'a> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_profile_name() {
        let res: Result<ProfileName, Error> = "".parse();
        assert!(matches!(res, Err(Error::User { .. })))
    }

    #[test]
    fn too_long_profile_name() {
        let name = "x".repeat(config::MAX_PROFILE_NAME_LENGTH + 1);
        let res: Result<ProfileName, Error> = name.parse();
        assert!(matches!(res, Err(Error::User { .. })))
    }

    #[test]
    fn profile_name_with_emoji_count() {
        // Edge case: too long when counting bytes, ok when counting chars.
        let res: Result<ProfileName, Error> = "Some Random Profile Name ✈️".parse();
        assert!(res.is_ok());
    }
}
