// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::{
    config,
    db::{models as m, DeferredTxConnection, ExclusiveTxConnection},
    encryption::{DataEncryptionKey, KeyEncryptionKey, Keychain},
    Error,
};

trait Migration {
    fn version() -> &'static str;

    fn description() -> &'static str;

    fn run(tx_conn: &mut DeferredTxConnection, keychain: &Keychain) -> Result<(), Error>;

    fn rollback(keychain: &Keychain) -> Result<(), Error>;
}

struct MigrationV0 {}

impl Migration for MigrationV0 {
    // TODO add version enum
    fn version() -> &'static str {
        "v0"
    }

    fn description() -> &'static str {
        "Creates SK-KEK, SK-DEK and Default account with an Ethereum/Polygon PoS wallet address."
    }

    fn run(tx_conn: &mut DeferredTxConnection, keychain: &Keychain) -> Result<(), Error> {
        // Generate SK-DEK and SK-KEK
        let sk_dek = DataEncryptionKey::random(config::SK_DEK_NAME.to_string())?;
        let sk_kek = KeyEncryptionKey::random(config::SK_KEK_NAME.to_string())?;
        keychain.put_local_unlocked(sk_kek)?;
        let sk_kek = keychain.get_sk_kek()?;

        // Create SK-DEK entity in DB
        let sk_dek_id = m::NewDataEncryptionKey::builder()
            .name(sk_dek.name())
            .build()
            .insert(tx_conn.as_mut())?;

        // Generate SK-DEK and store it encrypted with SK-KEK in DB
        let encrypted_dek = sk_dek.to_encrypted(&sk_kek)?;
        m::NewLocalEncryptedDek::builder()
            .dek_id(&sk_dek_id)
            .encrypted_dek(&encrypted_dek)
            .kek_name(sk_kek.name())
            .build()
            .insert(tx_conn.as_mut())?;

        let account_params = m::AccountParams::builder()
            .name(config::DEFAULT_ACCOUNT_NAME)
            .bundled_picture_name(config::DEFAULT_ACCOUNT_PICTURE_NAME)
            .build();
        let account_id =
            m::Account::create_eth_account(tx_conn, keychain, &account_params)?;

        m::LocalSettings::create(tx_conn.as_mut(), &account_id)?;

        // Record data migration
        m::NewDataMigration::builder()
            .version(Self::version())
            .description(Self::description())
            .build()
            .insert(tx_conn.as_mut())?;

        Ok(())
    }

    fn rollback(keychain: &Keychain) -> Result<(), Error> {
        // Allow rerunning the tx if there was a failure.
        // Database mutations are rolled back automatically by Diesel on error in the tx closure.
        keychain.soft_delete_sk_kek()
    }
}

pub fn run_all(tx_conn: ExclusiveTxConnection, keychain: &Keychain) -> Result<(), Error> {
    // We take an ExclusiveTxConnection as argument, because this method should be run in an
    // exclusive transaction, but called functions can be ran in deferred transactions.
    let mut tx_conn: DeferredTxConnection = tx_conn.into();

    if m::DataMigration::list_all(tx_conn.as_mut())?.is_empty() {
        match MigrationV0::run(&mut tx_conn, keychain) {
            Ok(()) => Ok(()),
            Err(err) => {
                MigrationV0::rollback(keychain)?;
                Err(err)
            }
        }
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;
    use crate::{
        app_core::tests::TmpCoreDir,
        db::{schema_migrations::run_migrations, ConnectionPool},
    };

    #[test]
    fn v0_rollback_works() -> Result<()> {
        let tmp = TmpCoreDir::new()?;
        let connection_pool = ConnectionPool::new(&tmp.db_file_path)?;
        let keychain = Keychain::new();

        // Schema migration
        connection_pool.exclusive_transaction(|mut tx_conn| {
            run_migrations(&mut tx_conn)?;
            Ok(())
        })?;

        // These migration attempts should fail.
        for _ in 0..10 {
            let res: Result<(), _> =
                connection_pool.deferred_transaction(|mut tx_conn| {
                    // Data migration
                    MigrationV0::run(&mut tx_conn, &keychain)?;
                    Err(Error::Retriable {
                        error: "Make diesel roll back the transaction".into(),
                    })
                });
            assert!(res.is_err());
            MigrationV0::rollback(&keychain)?;
        }
        // This should succeed.
        connection_pool.exclusive_transaction(|tx_conn| {
            // Data migration
            let mut tx_conn: DeferredTxConnection = tx_conn.into();
            MigrationV0::run(&mut tx_conn, &keychain)?;
            Ok(())
        })?;

        Ok(())
    }
}
