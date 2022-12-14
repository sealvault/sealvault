// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashSet, mem};

use dyn_clone::DynClone;
use generic_array::typenum::U32;
use lazy_static::lazy_static;
use url::Url;

use crate::db::deterministic_id::DeterministicId;
#[allow(deprecated)]
use crate::{
    config,
    db::{models as m, DeferredTxConnection, ExclusiveTxConnection},
    encryption::{DataEncryptionKey, KeyEncryptionKey, KeyName, Keychain},
    protocols::eth,
    public_suffix_list::PublicSuffixList,
    utils::{new_uuid, try_random_bytes},
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
        "Creates SK-KEK, SK-DEK and Default profile with an Ethereum/Polygon PoS wallet address."
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

        let profile_params = m::ProfileParams::builder()
            .name(config::DEFAULT_ACCOUNT_NAME)
            .bundled_picture_name(config::DEFAULT_ACCOUNT_PICTURE_NAME)
            .build();
        let profile_id =
            m::Profile::create_eth_profile(tx_conn, keychain, &profile_params)?;

        m::LocalSettings::create(tx_conn.as_mut(), &profile_id)?;

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
        let urls = vec!["https://quickswap.exchange/", "https://app.0xmint.io/"];
        urls.iter()
            .map(|u| Url::parse(u).expect("static ok"))
            .collect()
    }

    fn add_dapp(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        psl: &PublicSuffixList,
        profile_id: &str,
        dapp_url: Url,
    ) -> Result<(), Error> {
        let chain_id = eth::ChainId::default_dapp_chain();
        let dapp_id = m::Dapp::create_if_not_exists(tx_conn, dapp_url, psl)?;
        let params = m::CreateEthAddressParams::builder()
            .profile_id(profile_id)
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
            .profile_id(profile_id)
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
            let active_profile_id =
                m::LocalSettings::fetch_active_profile_id(tx_conn.as_mut())?;

            for url in Self::default_dapp_urls() {
                Self::add_dapp(tx_conn, keychain, psl, &active_profile_id, url)?
            }
        }

        Ok(())
    }

    fn rollback(&self, _: &Keychain) -> Result<(), Error> {
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct MigrationV2 {}

impl MigrationV2 {
    fn migrate_profiles(tx_conn: &mut DeferredTxConnection) -> Result<(), Error> {
        let profiles = m::Profile::list_all(tx_conn.as_mut())?;
        for mut profile in profiles.into_iter() {
            #[allow(deprecated)]
            let deprecated_account_entity = m::AccountEntity {
                uuid: &profile.uuid,
            };
            let deprecated_det_id = deprecated_account_entity.deterministic_id()?;
            // If deterministic ids don't match, it means the profile was put as account entity in
            // the db.
            if profile.deterministic_id == deprecated_det_id {
                // Switch the uuid temporarily so that we can insert the new one while the old one
                // remains. (There is a unique constraint on uuids).
                let original_uuid = mem::replace(&mut profile.uuid, new_uuid());

                // Compute deterministic id with new profile entity name (was called account before).
                let profile_entity = m::ProfileEntity {
                    uuid: &original_uuid,
                };
                let profile_det_id = profile_entity.deterministic_id()?;
                // Update the deterministic id
                let deprecated_det_id =
                    mem::replace(&mut profile.deterministic_id, profile_det_id);

                // Insert the profile with the updated deterministic id and temporary uuid.
                profile.insert(tx_conn.as_mut())?;

                // Update active profile id if needed.
                let active_profile_id =
                    m::LocalSettings::fetch_active_profile_id(tx_conn.as_mut())?;
                if active_profile_id == deprecated_det_id {
                    m::LocalSettings::set_active_profile_id(
                        tx_conn.as_mut(),
                        &profile.deterministic_id,
                    )?;
                }

                // Outer loop is expected to run only once since profile creation wasn't supported
                // at the time of the change from account to profile.
                let asymmetric_keys = m::AsymmetricKey::list_all(tx_conn.as_mut())?;
                for key in asymmetric_keys {
                    if key.profile_id == deprecated_det_id {
                        key.set_profile_id(tx_conn.as_mut(), &profile.deterministic_id)?;
                    }
                }

                // Remove old profile
                m::Profile::delete(tx_conn.as_mut(), &deprecated_det_id)?;

                // Put back original uuid now that it's not a duplicate.
                // This is the only place where setting uuid should be called.
                #[allow(deprecated)]
                profile.set_uuid(tx_conn.as_mut(), &original_uuid)?;
            }
        }
        Ok(())
    }

    fn migrate_profile_pictures(tx_conn: &mut DeferredTxConnection) -> Result<(), Error> {
        // Update profile pictures
        let profile_pictures = m::ProfilePicture::list_all(tx_conn.as_mut())?;
        for mut pp in profile_pictures.into_iter() {
            #[allow(deprecated)]
            let deprecated_pp_entity = m::AccountPictureEntity {
                image_hash: &pp.image_hash,
            };
            let deprecated_det_id = deprecated_pp_entity.deterministic_id()?;
            if pp.deterministic_id == deprecated_det_id {
                let temp_img_hash = try_random_bytes::<U32>()?.to_vec();
                let original_img_hash = mem::replace(&mut pp.image_hash, temp_img_hash);
                let pp_entity = m::ProfilePictureEntity {
                    image_hash: &original_img_hash,
                };
                let pp_det_id = pp_entity.deterministic_id()?;
                let deprecated_det_id = mem::replace(&mut pp.deterministic_id, pp_det_id);
                pp.insert(tx_conn.as_mut())?;

                let profiles = m::Profile::list_all(tx_conn.as_mut())?;
                for profile in profiles {
                    if profile.picture_id == deprecated_det_id {
                        profile.set_picture_id(tx_conn.as_mut(), &pp.deterministic_id)?;
                    }
                }

                m::ProfilePicture::delete(tx_conn.as_mut(), &deprecated_det_id)?;
                #[allow(deprecated)]
                pp.set_image_hash(tx_conn.as_mut(), &original_img_hash)?;
            }
        }
        Ok(())
    }
}

impl Migration for MigrationV2 {
    fn version(&self) -> &'static str {
        "v2"
    }

    fn description(&self) -> &'static str {
        // The entity name is hashed into the deterministic id which is why a data update is needed
        // in addition to the schema changes.
        "Update profile deterministic ids after accounts were renamed to profiles."
    }

    fn run(
        &self,
        tx_conn: &mut DeferredTxConnection,
        _: &Keychain,
        _: &PublicSuffixList,
    ) -> Result<(), Error> {
        MigrationV2::migrate_profiles(tx_conn)?;
        MigrationV2::migrate_profile_pictures(tx_conn)?;

        Ok(())
    }

    fn rollback(&self, _keychain: &Keychain) -> Result<(), Error> {
        Ok(())
    }
}

lazy_static! {
    static ref MIGRATIONS: Vec<Box<dyn Migration>> = vec![
        Box::new(MigrationV0 {}),
        Box::new(MigrationV1 {}),
        Box::new(MigrationV2 {})
    ];
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
    fn migration_versions_are_unique() {
        let mut versions: HashSet<&'static str> = Default::default();
        for m in MIGRATIONS.iter() {
            let _ = versions.insert(m.version());
        }
        assert_eq!(versions.len(), MIGRATIONS.len());
    }

    #[test]
    fn migrations_are_sorted() {
        for i in 0..(MIGRATIONS.len() - 1) {
            assert!(MIGRATIONS[i].version() < MIGRATIONS[i + 1].version())
        }
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

    /// Run v0 migration that sets up accounts instead of profile to simulate migration before
    /// deprecating accounts in favor of profiles.
    fn run_v0_migration_for_accounts(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
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

        #[allow(deprecated)]
        let profile_params = m::AccountParams::builder()
            .name(config::DEFAULT_ACCOUNT_NAME)
            .bundled_picture_name(config::DEFAULT_ACCOUNT_PICTURE_NAME)
            .build();
        #[allow(deprecated)]
        let profile_id =
            m::Account::create_eth_account(tx_conn, keychain, &profile_params)?;

        m::LocalSettings::create(tx_conn.as_mut(), &profile_id)?;

        Ok(())
    }

    #[test]
    fn v2_works() -> Result<()> {
        let tmp = TmpCoreDir::new()?;
        let connection_pool = ConnectionPool::new(&tmp.db_file_path)?;
        let keychain = Keychain::new();
        let psl = PublicSuffixList::new()?;

        // Run schema migrations and v0-v1 data migrations
        connection_pool.exclusive_transaction(|mut tx_conn| {
            run_migrations(&mut tx_conn)?;

            let mut tx_conn: DeferredTxConnection = tx_conn.into();

            run_v0_migration_for_accounts(&mut tx_conn, &keychain)?;

            let v1 = MigrationV1 {};
            v1.run(&mut tx_conn, &keychain, &psl)?;

            Ok(())
        })?;

        let (account, account_picture) = {
            let mut conn = connection_pool.connection()?;
            let accounts = m::Profile::list_all(&mut conn)?;
            let account_pictures = m::ProfilePicture::list_all(&mut conn)?;
            assert_eq!(accounts.len(), 1);
            assert_eq!(account_pictures.len(), 1);
            let account = accounts.into_iter().next().unwrap();
            let account_picture = account_pictures.into_iter().next().unwrap();
            (account, account_picture)
        };

        // Run data migration v2
        connection_pool.exclusive_transaction(|tx_conn| {
            let v2 = MigrationV2 {};
            let mut tx_conn: DeferredTxConnection = tx_conn.into();
            v2.run(&mut tx_conn, &keychain, &psl)?;

            Ok(())
        })?;

        {
            let mut conn = connection_pool.connection()?;

            let profiles = m::Profile::list_all(&mut conn)?;
            assert_eq!(profiles.len(), 1);
            let profile = profiles.into_iter().next().unwrap();
            assert_eq!(&profile.uuid, &account.uuid);
            assert_ne!(&profile.deterministic_id, &account.deterministic_id);
            let keys = m::AsymmetricKey::list_all(&mut conn)?;
            assert!(!keys.is_empty());
            for key in keys {
                assert_eq!(key.profile_id, profile.deterministic_id);
            }

            let profile_pics = m::ProfilePicture::list_all(&mut conn)?;
            assert_eq!(profile_pics.len(), 1);
            let profile_pic = profile_pics.into_iter().next().unwrap();
            assert_eq!(&profile_pic.image_hash, &account_picture.image_hash);
            assert_ne!(
                &profile_pic.deterministic_id,
                &account_picture.deterministic_id
            );
        }

        Ok(())
    }
}
