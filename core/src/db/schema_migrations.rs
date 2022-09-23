// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::db::ExclusiveTxConnection;
use crate::Error;
use diesel::SqliteConnection;
use diesel_migrations::{embed_migrations, EmbeddedMigrations, MigrationHarness};

// Ship Diesel migrations with the binary.
pub const MIGRATIONS: EmbeddedMigrations = embed_migrations!();

pub fn run_migrations(tx_conn: &mut ExclusiveTxConnection) -> Result<(), Error> {
    let conn: &mut SqliteConnection = tx_conn.as_mut();
    conn.run_pending_migrations(MIGRATIONS).map_err(|err| {
        log::error!("Failed to run schema migrations with error: {}", err);
        Error::Fatal {
            // Error type is opaque, best not expose it to Sentry in case it contains DB values.
            error: "Failed to run schema migrations".into(),
        }
    })?;

    Ok(())
}
