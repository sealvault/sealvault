// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use diesel::{prelude::*, SqliteConnection};
use generic_array::{typenum::U1, GenericArray};

use crate::{
    assets::load_profile_pic,
    db::{
        deterministic_id::{DeterministicId, EntityName},
        schema::profile_pictures,
    },
    utils::{blake3_hash, rfc3339_timestamp},
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable, Insertable)]
#[diesel(primary_key(deterministic_id))]
pub struct ProfilePicture {
    pub deterministic_id: String,
    pub image_name: Option<String>,
    pub image_hash: Vec<u8>,
    pub image: Vec<u8>,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl ProfilePicture {
    pub fn list_all(conn: &mut SqliteConnection) -> Result<Vec<ProfilePicture>, Error> {
        Ok(profile_pictures::table.load::<ProfilePicture>(conn)?)
    }

    pub fn list_names(conn: &mut SqliteConnection) -> Result<Vec<String>, Error> {
        use profile_pictures::dsl as pp;

        let names: Vec<Option<String>> =
            profile_pictures::table.select(pp::image_name).load(conn)?;

        Ok(names.into_iter().flatten().collect())
    }

    pub fn fetch_image(conn: &mut SqliteConnection, id: &str) -> Result<Vec<u8>, Error> {
        use profile_pictures::dsl as pp;

        let image = profile_pictures::table
            .filter(pp::deterministic_id.eq(id))
            .select(pp::image)
            .first(conn)?;

        Ok(image)
    }

    /// Insert a bundled profile picture into the database and return its deterministic id.
    pub fn insert_bundled(
        conn: &mut SqliteConnection,
        image_name: &str,
    ) -> Result<String, Error> {
        let image = load_profile_pic(image_name)?;
        let image_hash = blake3_hash(&image);
        let entity = ProfilePictureEntity {
            image_hash: image_hash.as_bytes(),
        };
        entity.create(conn, &image, Some(image_name))
    }

    pub fn delete(
        conn: &mut SqliteConnection,
        deterministic_id: &str,
    ) -> Result<(), Error> {
        use profile_pictures::dsl as pp;

        diesel::delete(
            profile_pictures::table.filter(pp::deterministic_id.eq(deterministic_id)),
        )
        .execute(conn)?;

        Ok(())
    }

    /// Deprecated, because image hash should match image. Only used in data migration to change
    /// temporarily to get around unique constraint.
    #[deprecated]
    pub fn set_image_hash(
        &self,
        conn: &mut SqliteConnection,
        hash: &[u8],
    ) -> Result<(), Error> {
        use profile_pictures::dsl as pp;

        diesel::update(
            profile_pictures::table
                .filter(pp::deterministic_id.eq(&self.deterministic_id)),
        )
        .set(pp::image_hash.eq(hash))
        .execute(conn)?;

        Ok(())
    }

    pub fn insert(&self, conn: &mut SqliteConnection) -> Result<(), Error> {
        diesel::insert_into(profile_pictures::table)
            .values(self)
            .execute(conn)?;
        Ok(())
    }
}

#[derive(Insertable)]
#[diesel(table_name = profile_pictures)]
pub struct ProfilePictureEntity<'a> {
    pub(crate) image_hash: &'a [u8],
}

impl<'a> ProfilePictureEntity<'a> {
    /// Insert an profile picture and return its deterministic id.
    fn create(
        &self,
        conn: &mut SqliteConnection,
        image: &[u8],
        image_name: Option<&str>,
    ) -> Result<String, Error> {
        use profile_pictures::dsl as pp;

        let deterministic_id = self.deterministic_id()?;
        let created_at = rfc3339_timestamp();
        diesel::insert_into(profile_pictures::table)
            .values((
                self,
                pp::deterministic_id.eq(&deterministic_id),
                pp::image.eq(image),
                pp::image_name.eq(image_name),
                pp::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(deterministic_id)
    }
}

impl<'a> DeterministicId<'a, &'a [u8], U1> for ProfilePictureEntity<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::ProfilePicture
    }

    fn unique_columns(&'a self) -> GenericArray<&'a [u8], U1> {
        [self.image_hash].into()
    }
}
