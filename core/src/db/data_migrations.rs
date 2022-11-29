// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::collections::HashSet;

use dyn_clone::DynClone;
use lazy_static::lazy_static;
use url::Url;

use crate::{
    config,
    db::{models as m, DeferredTxConnection, ExclusiveTxConnection},
    encryption::{DataEncryptionKey, KeyEncryptionKey, KeyName, Keychain},
    protocols::eth,
    public_suffix_list::PublicSuffixList,
    Error,
};

trait Migration: DynClone + Sync {
    // TODO add version enum
    fn version(&self) -> &'static str;

    fn description(&self) -> &'static str;

    fn run(
        &self,
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        psl: &PublicSuffixList,
    ) -> Result<(), Error>;

    fn rollback(&self, keychain: &Keychain) -> Result<(), Error>;
}

dyn_clone::clone_trait_object!(Migration);

#[derive(Debug, Clone)]
struct MigrationV0 {}

impl Migration for MigrationV0 {
    fn version(&self) -> &'static str {
        "v0"
    }

    fn description(&self) -> &'static str {
        "Creates SK-KEK, SK-DEK and Default account with an Ethereum/Polygon PoS wallet address."
    }

    fn run(
        &self,
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        _: &PublicSuffixList,
    ) -> Result<(), Error> {
        // Create SK-KEK and save it on keychain
        let sk_kek = KeyEncryptionKey::random(KeyName::SkKeyEncryptionKey)?;
        sk_kek.upsert_to_local_keychain(keychain)?;
        let sk_kek = KeyEncryptionKey::sk_kek(keychain)?;

        // Create SK-DEK and save it encrypted with SK-KEK in DB
        let sk_dek = DataEncryptionKey::random(KeyName::SkDataEncryptionKey)?;
        let sk_dek_id = m::NewDataEncryptionKey::builder()
            .name(sk_dek.name())
            .build()
            .insert(tx_conn.as_mut())?;
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

        Ok(())
    }

    fn rollback(&self, keychain: &Keychain) -> Result<(), Error> {
        // Allow rerunning the tx if there was a failure.
        // Database mutations are rolled back automatically by Diesel on error in the tx closure.
        KeyEncryptionKey::delete_from_keychain_if_exists(
            keychain,
            KeyName::SkKeyEncryptionKey,
        )
    }
}

#[derive(Debug, Clone)]
struct MigrationV1 {}

impl MigrationV1 {
    fn default_dapp_urls() -> Vec<Url> {
        let urls = vec!["https://app.uniswap.org/", "https://app.1inch.io/"];
        urls.iter()
            .map(|u| Url::parse(u).expect("static ok"))
            .collect()
    }

    fn add_dapp(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        psl: &PublicSuffixList,
        account_id: &str,
        dapp_url: Url,
    ) -> Result<(), Error> {
        let chain_id = eth::ChainId::default_dapp_chain();
        let dapp_id = m::Dapp::create_if_not_exists(tx_conn, dapp_url, psl)?;
        let params = m::CreateEthAddressParams::builder()
            .account_id(account_id)
            .chain_id(chain_id)
            .dapp_id(Some(&dapp_id))
            .build();
        m::Address::create_eth_key_and_address(tx_conn, keychain, &params)?;
        // We're adding the dapp session here, because Uniswap makes two simultaneous requests on
        // connect (`eth_requestAccounts` and `eth_chainId`) and as both try to inject the session
        // on first connect, one of them is rejected by Sqlite and the Uniswap front end doesn't
        // retry, just hangs.
        let params = m::NewDappSessionParams::builder()
            .dapp_id(&dapp_id)
            .account_id(account_id)
            .chain_id(chain_id)
            .build();
        m::LocalDappSession::create_eth_session(tx_conn, &params)?;
        Ok(())
    }
}

impl Migration for MigrationV1 {
    fn version(&self) -> &'static str {
        "v1"
    }

    fn description(&self) -> &'static str {
        "Adds default dapps on default dapp chain if the user doesn't have any dapps."
    }

    fn run(
        &self,
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        psl: &PublicSuffixList,
    ) -> Result<(), Error> {
        let dapps = m::Dapp::list_all(tx_conn.as_mut())?;
        if dapps.is_empty() {
            let active_account_id =
                m::LocalSettings::fetch_active_account_id(tx_conn.as_mut())?;

            for url in Self::default_dapp_urls() {
                Self::add_dapp(tx_conn, keychain, psl, &active_account_id, url)?
            }
        }

        Ok(())
    }

    fn rollback(&self, _: &Keychain) -> Result<(), Error> {
        Ok(())
    }
}

lazy_static! {
    static ref MIGRATIONS: Vec<Box<dyn Migration>> =
        vec![Box::new(MigrationV0 {}), Box::new(MigrationV1 {})];
}

pub fn run_all(
    tx_conn: ExclusiveTxConnection,
    keychain: &Keychain,
    psl: &PublicSuffixList,
) -> Result<(), Error> {
    // We take an ExclusiveTxConnection as argument, because this method should be run in an
    // exclusive transaction, but called functions can be ran in deferred transactions.
    let mut tx_conn: DeferredTxConnection = tx_conn.into();

    let applied_versions: HashSet<String> =
        m::DataMigration::list_versions_sorted(tx_conn.as_mut())?
            .into_iter()
            .collect();

    for migration in MIGRATIONS.iter() {
        if !applied_versions.contains(migration.version()) {
            match migration.run(&mut tx_conn, keychain, psl) {
                Ok(_) => {
                    m::NewDataMigration::builder()
                        .version(migration.version())
                        .description(migration.description())
                        .build()
                        .insert(tx_conn.as_mut())?;
                }
                Err(err) => {
                    migration.rollback(keychain)?;
                    return Err(err);
                }
            }
        }
    }

    Ok(())
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
    fn migrations_are_sorted() -> Result<()> {
        for i in 0..(MIGRATIONS.len() - 1) {
            assert!(MIGRATIONS[i].version() < MIGRATIONS[i + 1].version())
        }

        Ok(())
    }

    #[test]
    fn runs_all_migrations() -> Result<()> {
        let tmp = TmpCoreDir::new()?;
        let connection_pool = ConnectionPool::new(&tmp.db_file_path)?;
        let keychain = Keychain::new();
        let psl = PublicSuffixList::new()?;

        connection_pool.exclusive_transaction(|mut tx_conn| {
            // Schema migration
            run_migrations(&mut tx_conn)?;
            run_all(tx_conn, &keychain, &psl)
        })?;

        let mut conn = connection_pool.connection()?;
        let versions = m::DataMigration::list_versions_sorted(&mut conn)?;
        assert_eq!(versions.len(), MIGRATIONS.len());

        for i in 0..(versions.len() - 1) {
            assert!(versions[i] < versions[i + 1])
        }

        Ok(())
    }

    #[test]
    fn v0_rollback_works() -> Result<()> {
        let tmp = TmpCoreDir::new()?;
        let connection_pool = ConnectionPool::new(&tmp.db_file_path)?;
        let keychain = Keychain::new();
        let psl = PublicSuffixList::new()?;

        connection_pool.exclusive_transaction(|mut tx_conn| {
            run_migrations(&mut tx_conn)?;
            Ok(())
        })?;

        let migration = MigrationV0 {};

        // These migration attempts should fail.
        for _ in 0..10 {
            let res: Result<(), _> =
                connection_pool.deferred_transaction(|mut tx_conn| {
                    // Data migration
                    migration.run(&mut tx_conn, &keychain, &psl)?;
                    Err(Error::Retriable {
                        error: "Make diesel roll back the transaction".into(),
                    })
                });
            assert!(res.is_err());
            migration.rollback(&keychain)?;
        }
        // This should succeed.
        connection_pool.exclusive_transaction(|tx_conn| {
            // Data migration
            let mut tx_conn: DeferredTxConnection = tx_conn.into();
            migration.run(&mut tx_conn, &keychain, &psl)?;
            Ok(())
        })?;

        Ok(())
    }
}
