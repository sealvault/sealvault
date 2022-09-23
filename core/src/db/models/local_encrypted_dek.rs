// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::db::schema::local_encrypted_deks;

use crate::encryption::EncryptionOutput;

use crate::utils::rfc3339_timestamp;
use crate::Error;
use diesel::prelude::*;

use typed_builder::TypedBuilder;

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
pub struct LocalEncryptedDek {
    pub id: i64,
    pub dek_id: String,
    pub encrypted_dek: EncryptionOutput,
    pub kek_name: String,
    pub created_at: String,
    pub updated_at: String,
}

#[derive(TypedBuilder, Insertable)]
#[diesel(table_name = local_encrypted_deks)]
pub struct NewLocalEncryptedDek<'a> {
    dek_id: &'a str,
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
