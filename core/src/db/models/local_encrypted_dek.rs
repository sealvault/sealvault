// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::prelude::*;
use typed_builder::TypedBuilder;

use crate::{
    db::{schema::local_encrypted_deks, DeterministicId},
    encryption::EncryptionOutput,
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
pub struct LocalEncryptedDek {
    pub id: i32,
    pub dek_id: DeterministicId,
    pub encrypted_dek: EncryptionOutput,
    pub kek_name: String,
    pub created_at: String,
    pub updated_at: String,
}

impl LocalEncryptedDek {
    pub fn fetch_id(
        conn: &mut SqliteConnection,
        dek_id: &DeterministicId,
        kek_name: &str,
    ) -> Result<Option<i32>, Error> {
        use local_encrypted_deks::dsl as led;

        // There is a `UNIQUE (dek_id, kek_name)` constraint on the table.
        let id = local_encrypted_deks::table
            .filter(led::dek_id.eq(dek_id).and(led::kek_name.eq(kek_name)))
            .select(led::id)
            .first(conn)
            .optional()?;

        Ok(id)
    }
    pub fn set_encrypted_dek(
        conn: &mut SqliteConnection,
        id: i32,
        encrypted_dek: &EncryptionOutput,
    ) -> Result<(), Error> {
        use local_encrypted_deks::dsl as led;

        let updated_at = rfc3339_timestamp();

        diesel::update(local_encrypted_deks::table.find(id))
            .set((
                led::encrypted_dek.eq(encrypted_dek),
                led::updated_at.eq(&updated_at),
            ))
            .execute(conn)?;

        Ok(())
    }
}

#[derive(TypedBuilder, Insertable)]
#[diesel(table_name = local_encrypted_deks)]
pub struct NewLocalEncryptedDek<'a> {
    dek_id: &'a DeterministicId,
    encrypted_dek: &'a EncryptionOutput,
    kek_name: &'a str,
}

impl<'a> NewLocalEncryptedDek<'a> {
    pub fn insert(&self, conn: &mut SqliteConnection) -> Result<(), Error> {
        use local_encrypted_deks::dsl as led;

        let created_at = rfc3339_timestamp();

        diesel::insert_into(local_encrypted_deks::table)
            .values((self, led::created_at.eq(&created_at)))
            .execute(conn)?;

        Ok(())
    }
}
