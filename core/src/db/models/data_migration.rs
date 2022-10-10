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
        schema::data_migrations,
    },
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
pub struct DataMigration {
    pub deterministic_id: String,
    pub version: String,
    pub description: String,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl DataMigration {
    pub fn list_all(conn: &mut SqliteConnection) -> Result<Vec<DataMigration>, Error> {
        Ok(data_migrations::table.load::<DataMigration>(conn)?)
    }
}

#[derive(TypedBuilder, Insertable)]
#[diesel(table_name = data_migrations)]
pub struct NewDataMigration<'a> {
    #[builder(setter(into))]
    version: &'a str,
    #[builder(setter(into))]
    description: Option<&'a str>,
}

impl<'a> NewDataMigration<'a> {
    /// Create a new data migration and return its deterministic id.
    pub fn insert(&self, conn: &mut SqliteConnection) -> Result<String, Error> {
        use data_migrations::dsl as dm;

        let deterministic_id = self.deterministic_id()?;
        let created_at = rfc3339_timestamp();

        diesel::insert_into(data_migrations::table)
            .values((
                self,
                dm::deterministic_id.eq(&deterministic_id),
                dm::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(deterministic_id)
    }
}

impl<'a> DeterministicId<'a, &'a str, U1> for NewDataMigration<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::DataMigration
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U1> {
        [self.version].into()
    }
}
