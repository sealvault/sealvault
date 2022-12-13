// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::prelude::*;

use crate::{db::schema::local_settings, Error};

#[derive(Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(table_name = local_settings)]
pub struct LocalSettings {
    pub id: String,
    pub profile_id: String,
}

const SINGLETON_ID: &str = "local_settings";

impl LocalSettings {
    pub fn create(
        connection: &mut SqliteConnection,
        profile_id: &str,
    ) -> Result<(), Error> {
        use local_settings::dsl as ls;

        diesel::insert_into(local_settings::table)
            .values((ls::id.eq(SINGLETON_ID), ls::profile_id.eq(profile_id)))
            .execute(connection)?;

        Ok(())
    }

    pub fn fetch_active_profile_id(
        connection: &mut SqliteConnection,
    ) -> Result<String, Error> {
        use local_settings::dsl as ls;

        let profile_id = local_settings::table
            .find(&SINGLETON_ID)
            .select(ls::profile_id)
            .first(connection)?;
        Ok(profile_id)
    }

    pub fn set_active_profile_id(
        connection: &mut SqliteConnection,
        profile_id: &str,
    ) -> Result<(), Error> {
        use local_settings::dsl as ls;

        diesel::update(local_settings::table.filter(ls::id.eq(&SINGLETON_ID)))
            .set(ls::profile_id.eq(profile_id))
            .execute(connection)?;
        Ok(())
    }
}
