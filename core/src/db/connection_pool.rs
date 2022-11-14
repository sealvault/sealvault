// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    fmt::{Debug, Formatter},
    path::{Path, PathBuf},
    time::Duration,
};

use diesel::{
    connection::SimpleConnection,
    r2d2::{ConnectionManager, Pool, PooledConnection},
    Connection, SqliteConnection,
};

use crate::{async_runtime as rt, config, db::models as m, Error};

/// A Sqlite connection pool.
#[derive(Debug)]
pub struct ConnectionPool {
    pool: Pool<ConnectionManager<SqliteConnection>>,
    db_path: PathBuf,
}

type PooledSqliteConnection = PooledConnection<ConnectionManager<SqliteConnection>>;

impl ConnectionPool {
    pub fn new(db_path: &str) -> Result<Self, Error> {
        let manager = ConnectionManager::new(db_path);
        let pool = Pool::builder()
            .max_size(config::DB_CONNECTION_POOL_SIZE)
            .connection_customizer(Box::new(ConnectionOptions {
                // Needed to allow concurrent transactions
                busy_timeout: config::DB_BUSY_TIMEOUT,
            }))
            .build(manager)?;
        Ok(Self {
            pool,
            db_path: db_path.into(),
        })
    }

    /// Get a Sqlite connection.
    pub fn connection(&self) -> Result<PooledSqliteConnection, Error> {
        let conn = self.pool.get()?;
        Ok(conn)
    }

    /// Start a deferred transaction.
    pub fn deferred_transaction<T, F>(&self, callback: F) -> Result<T, Error>
    where
        F: FnOnce(DeferredTxConnection) -> Result<T, Error>,
    {
        let mut conn = self.connection()?;
        conn.transaction::<T, Error, _>(|conn| {
            let tx_conn = DeferredTxConnection(conn);
            callback(tx_conn)
        })
    }

    // TODO figure out how to avoid 'static bound on closure. It's annoying, because it requires
    // moving everything inside the closure.
    pub async fn deferred_transaction_async<T, F>(&self, callback: F) -> Result<T, Error>
    where
        F: FnOnce(DeferredTxConnection) -> Result<T, Error> + Send + 'static,
        T: Send + 'static,
    {
        let pool = self.pool.clone();
        rt::spawn_blocking(move || {
            let mut conn = pool.get()?;
            conn.transaction::<T, Error, _>(|conn| {
                let tx_conn = DeferredTxConnection(conn);
                callback(tx_conn)
            })
        })
        .await?
    }

    /// Start an exclusive transaction.
    pub fn exclusive_transaction<T, F>(&self, callback: F) -> Result<T, Error>
    where
        F: FnOnce(ExclusiveTxConnection) -> Result<T, Error>,
    {
        let mut connection = self.connection()?;
        connection.exclusive_transaction::<T, Error, _>(|conn| {
            let tx_conn = ExclusiveTxConnection(conn);
            callback(tx_conn)
        })
    }

    /// Creates a backup of the database and stores it a file path.
    pub fn backup(&self, to_path: &Path) -> Result<(), Error> {
        let db_path = self.db_path.as_path();

        // Flush WAL to the DB file. Can't be part of the exclusive transaction as it does its own
        // locking.
        let mut conn = self.connection()?;
        conn.batch_execute("PRAGMA wal_checkpoint(FULL);")?;

        // Acquire lock on DB for copy.
        self.exclusive_transaction(|_| {
            let mut backup_file =
                std::fs::File::create(to_path).map_err(|err| Error::Retriable {
                    error: format!("Failed to create backup file: {err}"),
                })?;

            let mut db_file =
                std::fs::File::open(db_path).map_err(|err| Error::Retriable {
                    error: format!("Failed to open DB file: {err}"),
                })?;

            std::io::copy(&mut db_file, &mut backup_file).map_err(|err| {
                Error::Retriable {
                    error: format!("Failed to copy DB file to backup file: {err}"),
                }
            })
        })?;

        Self::verify_backup(to_path)?;

        Ok(())
    }

    fn verify_backup(backup_path: &Path) -> Result<(), Error> {
        let backup_path = backup_path.to_str().ok_or_else(|| Error::Fatal {
            error: "Failed to convert backup path to utf-8".into(),
        })?;
        let backup_cp = ConnectionPool::new(backup_path)?;
        let mut backup_conn = backup_cp.connection()?;

        let deks = m::DataEncryptionKey::list_names(&mut backup_conn)?;
        if deks.is_empty() {
            Err(Error::Fatal {
                error: "No DEKs in backup".into(),
            })
        } else {
            Ok(())
        }
    }
}

/// A deferred Sqlite transaction. Functions that execute queries should take this as argument
/// instead of `SqliteConnection` if they should be executed in a deferred transaction.
pub struct DeferredTxConnection<'a>(&'a mut SqliteConnection);

impl<'a> AsMut<SqliteConnection> for DeferredTxConnection<'a> {
    fn as_mut(&mut self) -> &mut SqliteConnection {
        self.0
    }
}

impl<'a> Debug for DeferredTxConnection<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeferredTxConnection").finish()
    }
}

/// An exclusive Sqlite transaction. Functions that execute queries should take this as argument
/// instead of `SqliteConnection` if they should be executed in an exclusive transaction.
pub struct ExclusiveTxConnection<'a>(&'a mut SqliteConnection);

impl<'a> AsMut<SqliteConnection> for ExclusiveTxConnection<'a> {
    fn as_mut(&mut self) -> &mut SqliteConnection {
        self.0
    }
}

// Exclusive transaction guarantees are superset of deferred guarantees, so it's safe to go from
// exclusive to deferred, but not the other way around.
impl<'a> From<ExclusiveTxConnection<'a>> for DeferredTxConnection<'a> {
    fn from(tx_conn: ExclusiveTxConnection<'a>) -> Self {
        DeferredTxConnection(tx_conn.0)
    }
}

impl<'a> Debug for ExclusiveTxConnection<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExclusiveTxConnection").finish()
    }
}

// Based on https://stackoverflow.com/a/57717533
#[derive(Debug)]
pub struct ConnectionOptions {
    pub busy_timeout: Duration,
}

impl diesel::r2d2::CustomizeConnection<SqliteConnection, diesel::r2d2::Error>
    for ConnectionOptions
{
    fn on_acquire(&self, conn: &mut SqliteConnection) -> Result<(), diesel::r2d2::Error> {
        let timeout = self.busy_timeout.as_millis();
        let query = &format!(
            "
            PRAGMA busy_timeout = {timeout};
            PRAGMA journal_mode = WAL;
            PRAGMA synchronous = NORMAL;
            PRAGMA foreign_keys = ON;
        "
        );
        conn.batch_execute(query)
            .map_err(diesel::r2d2::Error::QueryError)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;
    use crate::{
        db::{data_migrations, schema_migrations::run_migrations},
        encryption::Keychain,
    };

    #[test]
    fn backup() -> Result<()> {
        let tmp_dir = tempfile::tempdir().expect("creates temp dir");
        let db_path = tmp_dir.path().join("db.sqlite3");
        let backup_path = tmp_dir.path().join("backup.sqlite3");

        // Create mock db
        let connection_pool = ConnectionPool::new(db_path.to_str().expect("ok utf-8"))?;
        let keychain = Keychain::new();

        connection_pool.exclusive_transaction(|mut tx_conn| {
            run_migrations(&mut tx_conn)?;
            data_migrations::run_all(tx_conn, &keychain)
        })?;

        // Create backup (also checks integrity)
        connection_pool.backup(backup_path.as_path())?;

        // Make sure backup was written to the path that we requested.
        let backup_file = std::fs::File::open(backup_path.as_path())?;
        assert_ne!(backup_file.metadata()?.len(), 0);

        Ok(())
    }
}
