// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::db::schema::local_settings;
use crate::Error;
use diesel::prelude::*;

#[derive(Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(table_name = local_settings)]
pub struct LocalSettings {
    pub id: String,
    pub account_id: String,
}

const SINGLETON_ID: &str = "local_settings";

impl LocalSettings {
    pub fn create(
        connection: &mut SqliteConnection,
        account_id: &str,
    ) -> Result<(), Error> {
        use local_settings::dsl as ls;

        diesel::insert_into(local_settings::table)
            .values((ls::id.eq(SINGLETON_ID), ls::account_id.eq(account_id)))
            .execute(connection)?;

        Ok(())
    }

    pub fn fetch_active_account_id(
        connection: &mut SqliteConnection,
    ) -> Result<String, Error> {
        use local_settings::dsl as ls;

        let account_id = local_settings::table
            .find(&SINGLETON_ID)
            .select(ls::account_id)
            .first(connection)?;
        Ok(account_id)
    }
}
