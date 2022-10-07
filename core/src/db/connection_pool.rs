// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    fmt::{Debug, Formatter},
    time::Duration,
};

use diesel::{
    connection::SimpleConnection,
    r2d2::{ConnectionManager, Pool, PooledConnection},
    Connection, SqliteConnection,
};

use crate::{async_runtime as rt, config, Error};

/// A Sqlite connection pool.
#[derive(Debug)]
pub struct ConnectionPool {
    pool: Pool<ConnectionManager<SqliteConnection>>,
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
        Ok(Self { pool })
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
        (|| {
            let timeout = self.busy_timeout.as_millis();
            conn.batch_execute(&format!("PRAGMA busy_timeout = {};", timeout))?;
            conn.batch_execute(
                "PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;",
            )?;
            conn.batch_execute("PRAGMA foreign_keys = ON;")?;
            Ok(())
        })()
        .map_err(diesel::r2d2::Error::QueryError)
    }
}
