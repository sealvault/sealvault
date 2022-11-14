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
        schema::{data_encryption_keys, local_encrypted_deks},
    },
    encryption::{DataEncryptionKey as EncDek, EncryptionOutput, KeyEncryptionKey},
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
pub struct DataEncryptionKey {
    pub deterministic_id: String,
    pub name: String,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl DataEncryptionKey {
    pub fn list_names(connection: &mut SqliteConnection) -> Result<Vec<String>, Error> {
        use data_encryption_keys::dsl as dek;

        let results = data_encryption_keys::table
            .select(dek::name)
            .load(connection)?;

        Ok(results)
    }

    /// Fetch a DEK from the DB by name and decrypt it.
    /// Returns the DEK id and the decrypted DEK.
    pub fn fetch_dek(
        connection: &mut SqliteConnection,
        dek_name: &str,
        kek: &KeyEncryptionKey,
    ) -> Result<(String, EncDek), Error> {
        use data_encryption_keys::dsl as dek;
        use local_encrypted_deks::dsl as led;

        let (dek_id, encrypted_dek) = data_encryption_keys::table
            .inner_join(
                local_encrypted_deks::table.on(dek::deterministic_id.eq(led::dek_id)),
            )
            .filter(dek::name.eq(dek_name).and(led::kek_name.eq(kek.name())))
            .select((dek::deterministic_id, led::encrypted_dek))
            .first::<(String, EncryptionOutput)>(connection)?;

        let dek = EncDek::from_encrypted(dek_name.into(), &encrypted_dek, kek)?;
        Ok((dek_id, dek))
    }
}

#[derive(TypedBuilder, Insertable)]
#[diesel(table_name = data_encryption_keys)]
pub struct NewDataEncryptionKey<'a> {
    #[builder(setter(into))]
    name: &'a str,
}

impl<'a> NewDataEncryptionKey<'a> {
    /// Create a new data encryption key and return its deterministic id.
    pub fn insert(&self, conn: &mut SqliteConnection) -> Result<String, Error> {
        use data_encryption_keys::dsl as dek;

        let deterministic_id = self.deterministic_id()?;
        let created_at = rfc3339_timestamp();

        diesel::insert_into(data_encryption_keys::table)
            .values((
                self,
                dek::deterministic_id.eq(&deterministic_id),
                dek::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(deterministic_id)
    }
}

impl<'a> DeterministicId<'a, &'a str, U1> for NewDataEncryptionKey<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::DataEncryptionKey
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U1> {
        [self.name].into()
    }
}
