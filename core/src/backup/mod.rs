// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

mod backup_error;
mod backup_scheme;
mod create;
mod metadata;
mod restore;
mod setup;

// File names inside the backup zip
pub(in crate::backup) const ENCRYPTED_BACKUP_FILE_NAME: &str = "backup.sqlite3.encrypted";

pub(in crate::backup) const METADATA_FILE_NAME: &str = "metadata.json";

pub use backup_error::BackupError;
pub use create::create_backup;
pub use metadata::BackupMetadata;
pub use restore::{find_latest_backup, restore_backup, BackupRestoreData};
pub use setup::{
    disable_backup, display_backup_password, is_backup_enabled, set_up_or_rotate_backup,
};

#[cfg(test)]
mod tests {
    use std::{fs, fs::File, path::Path, sync::Arc};

    use anyhow::Result;
    use tempfile::NamedTempFile;

    use super::*;
    use crate::{
        app_core::tests::{CoreResourcesMock, TmpCoreDir},
        backup::{
            backup_scheme::BackupScheme,
            create::db_backup,
            metadata::MetadataFromFileName,
            restore::{
                backup_metadata_from_zip, find_latest_restorable_backup,
                restore_backup_inner,
            },
        },
        db::{
            data_migrations, models as m, schema_migrations::run_migrations,
            ConnectionPool,
        },
        device::{DeviceIdentifier, DeviceName},
        encryption::{KdfNonce, KdfSecret, Keychain},
        protocols::eth,
        resources::CoreResourcesI,
        CoreArgs,
    };

    struct BackupTest {
        pub resources: Arc<CoreResourcesMock>,
    }

    impl BackupTest {
        fn new() -> Result<Self> {
            let tmp_dir = TmpCoreDir::new()?;
            let resources = Arc::new(CoreResourcesMock::new(tmp_dir)?);

            resources
                .connection_pool()
                .exclusive_transaction(|mut tx_conn| {
                    run_migrations(&mut tx_conn)?;
                    data_migrations::run_all(
                        tx_conn,
                        resources.keychain(),
                        resources.public_suffix_list(),
                    )
                })?;

            Ok(Self { resources })
        }

        fn backup_dir(&self) -> &Path {
            self.resources.backup_dir().expect("has backup dir")
        }

        fn setup_or_rotate_backup(&self) -> Result<()> {
            set_up_or_rotate_backup(
                self.resources.connection_pool(),
                self.resources.keychain(),
                self.resources.device_id(),
            )?;
            Ok(())
        }

        fn backup_password(&self) -> Result<String> {
            let res = display_backup_password(self.resources.keychain())?;
            Ok(res)
        }

        fn create_backup(&self) -> Result<BackupMetadata> {
            let metadata = create_backup(self.resources.clone())?;
            Ok(metadata)
        }

        fn create_backup_without_deleting_outdated(&self) -> Result<BackupMetadata> {
            let metadata = db_backup(
                self.resources.as_ref(),
                self.resources.backup_dir().unwrap(),
            )?;
            Ok(metadata)
        }

        fn add_key(&self) -> Result<()> {
            self.resources
                .connection_pool()
                .deferred_transaction(|mut tx_conn| {
                    let profile = m::Profile::list_all(tx_conn.as_mut())?
                        .into_iter()
                        .next()
                        .expect("there is an profile");
                    let params = m::CreateEthAddressParams::builder()
                        .profile_id(&profile.deterministic_id)
                        .chain_id(eth::ChainId::default_wallet_chain())
                        .is_profile_wallet(true)
                        .build();
                    m::Address::create_eth_key_and_address(
                        &mut tx_conn,
                        &self.resources.keychain(),
                        &params,
                    )?;
                    Ok(())
                })?;
            Ok(())
        }

        fn backup_file_names(&self) -> Result<Vec<String>> {
            let mut file_names: Vec<String> = Default::default();
            let entries = fs::read_dir(self.backup_dir())?;
            for entry in entries {
                let file_name = entry?.file_name();
                let file_name = file_name.to_str().expect("valid string filename");
                file_names.push(file_name.into());
            }
            Ok(file_names)
        }

        fn backup_versions_in_dir(&self) -> Result<Vec<i64>> {
            let mut res: Vec<i64> = Default::default();
            for file_name in self.backup_file_names()? {
                let meta: MetadataFromFileName = file_name.parse()?;
                res.push(meta.backup_version);
            }
            Ok(res)
        }
    }

    struct RestoreTest {
        resources: Arc<CoreResourcesMock>,
        restore_to: NamedTempFile,
    }

    impl RestoreTest {
        fn new(backup: BackupTest) -> Result<Self> {
            let BackupTest { resources } = backup;
            let mut resources = Arc::try_unwrap(resources)
                .expect("resources aren't held when BackupTest is owned");

            // Create new keychain to simulate running on other device but copy over kdf secret
            // which is synced.
            let kdf_secret =
                KdfSecret::from_keychain(resources.keychain(), resources.device_id())?;
            let keychain = Keychain::new();
            kdf_secret.save_to_keychain(&keychain, resources.device_id())?;
            resources.set_keychain(keychain);
            resources.set_device_id("restore-device-id".parse()?);

            Ok(Self {
                resources: Arc::new(resources),
                restore_to: NamedTempFile::new()?,
            })
        }

        fn restore(
            &self,
            password: &str,
            metadata: &BackupMetadata,
        ) -> Result<BackupMetadata> {
            let restore_from = self
                .resources
                .backup_dir()
                .unwrap()
                .join(metadata.backup_file_name());

            let backup_dir = Some(
                self.resources
                    .backup_dir()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_string(),
            );
            let db_file_path = self.restore_to.path().to_str().unwrap().to_string();

            let core_args = CoreArgs {
                device_id: self.resources.device_id().to_string(),
                device_name: self.resources.device_name().to_string(),
                // This is not used for restore
                cache_dir: "".into(),
                db_file_path,
                backup_dir,
            };

            let backup_metadata = restore_backup_inner(
                core_args,
                restore_from.as_path(),
                password,
                self.resources.keychain(),
            )?;

            Ok(backup_metadata)
        }

        fn verify_can_decrypt_key(&self) -> Result<()> {
            let connection_pool = ConnectionPool::new(
                self.restore_to
                    .path()
                    .to_str()
                    .expect("path converts to str"),
            )?;
            let _ = connection_pool.deferred_transaction(|mut tx_conn| {
                let profiles = m::Profile::list_all(tx_conn.as_mut())?;
                let profile = profiles.first().expect("there is a profile");
                let address_id = m::Address::fetch_eth_wallet_id(
                    &mut tx_conn,
                    &profile.deterministic_id,
                    eth::ChainId::default_wallet_chain(),
                )?;
                // Uses SK-KEK to decrypt
                m::Address::fetch_eth_signing_key(
                    &mut tx_conn,
                    self.resources.keychain(),
                    &address_id,
                )
            })?;
            Ok(())
        }

        fn verify(&self, password: &str, backup_metadata: &BackupMetadata) -> Result<()> {
            let restore_metadata = self.restore(password, backup_metadata)?;
            self.verify_can_decrypt_key()?;
            assert_eq!(backup_metadata, &restore_metadata);
            Ok(())
        }
    }

    #[test]
    fn can_restore_db_backup() -> Result<()> {
        let backup = BackupTest::new()?;
        backup.setup_or_rotate_backup()?;
        let password = backup.backup_password()?;
        let backup_metadata = backup.create_backup()?;
        let mut conn = backup.resources.connection_pool().connection()?;
        m::LocalSettings::fetch_backup_timestamp(&mut conn)?
            .expect("there is backup timestamp");

        let backup_enabled = is_backup_enabled(backup.resources.connection_pool())?;
        assert!(backup_enabled);

        let restore = RestoreTest::new(backup)?;
        restore.verify(&password, &backup_metadata)?;

        Ok(())
    }

    #[test]
    fn can_restore_after_multiple_backup() -> Result<()> {
        let backup = BackupTest::new()?;
        backup.setup_or_rotate_backup()?;
        let password = backup.backup_password()?;

        // First backup
        let backup_metadata = backup.create_backup()?;
        let initial_backup_version = backup_metadata.backup_version;
        assert!(initial_backup_version > 0);

        backup.add_key()?;
        let backup_metadata = backup.create_backup()?;
        assert!(initial_backup_version < backup_metadata.backup_version);

        // Test cleanup
        let versions_in_dir = backup.backup_versions_in_dir()?;
        assert_eq!(versions_in_dir.len(), 1);
        assert_eq!(
            *versions_in_dir.first().unwrap(),
            backup_metadata.backup_version
        );

        let restore = RestoreTest::new(backup)?;
        restore.verify(&password, &backup_metadata)?;

        Ok(())
    }

    #[test]
    fn can_rotate_password() -> Result<()> {
        let backup = BackupTest::new()?;
        backup.setup_or_rotate_backup()?;
        backup.setup_or_rotate_backup()?;
        let password = backup.backup_password()?;
        let backup_metadata = backup.create_backup()?;

        let restore = RestoreTest::new(backup)?;
        restore.verify(&password, &backup_metadata)?;

        Ok(())
    }

    #[test]
    fn can_rollback_setup() -> Result<()> {
        let backup = BackupTest::new()?;

        backup.setup_or_rotate_backup()?;
        disable_backup(
            backup.resources.connection_pool(),
            backup.resources.keychain(),
            backup.resources.device_id(),
        )?;

        // Shouldn't create backup after rollback
        let backup_enabled = is_backup_enabled(backup.resources.connection_pool())?;
        assert!(!backup_enabled);

        backup.setup_or_rotate_backup()?;
        let password = backup.backup_password()?;
        let backup_metadata = backup.create_backup()?;

        let restore = RestoreTest::new(backup)?;
        restore.verify(&password, &backup_metadata)?;

        Ok(())
    }

    #[test]
    fn can_rollback_rotate() -> Result<()> {
        let backup = BackupTest::new()?;

        backup.setup_or_rotate_backup()?;
        backup.setup_or_rotate_backup()?;
        disable_backup(
            backup.resources.connection_pool(),
            backup.resources.keychain(),
            backup.resources.device_id(),
        )?;

        let backup_enabled = is_backup_enabled(backup.resources.connection_pool())?;
        assert!(!backup_enabled);

        backup.setup_or_rotate_backup()?;
        let password = backup.backup_password()?;

        let backup_metadata = backup.create_backup()?;

        let restore = RestoreTest::new(backup)?;
        restore.verify(&password, &backup_metadata)?;

        Ok(())
    }

    #[test]
    fn empty_dir_ok_for_finding_restorable() -> Result<()> {
        let backup = BackupTest::new()?;
        let res = find_latest_restorable_backup(backup.backup_dir())?;
        assert!(res.is_none());
        Ok(())
    }

    #[test]
    fn finds_restorable() -> Result<()> {
        let backup = BackupTest::new()?;
        backup.setup_or_rotate_backup()?;
        let _ = backup.create_backup_without_deleting_outdated()?;
        backup.add_key()?;
        let metadata = backup.create_backup_without_deleting_outdated()?;

        // Make sure it can handle an unexpected file name in the directory
        File::create(backup.backup_dir().join("some-random-file.zip"))?;

        let res = find_latest_restorable_backup(backup.backup_dir())?.unwrap();

        assert_eq!(metadata.timestamp, res.timestamp);

        let path = Path::new(&res.file_path);
        let meta_from_zip = backup_metadata_from_zip(path)?;
        assert_eq!(meta_from_zip, metadata);

        Ok(())
    }

    #[test]
    fn device_id_from_filename_ok() -> Result<()> {
        let device_name: DeviceName = "test-device".parse()?;
        let device_id: DeviceIdentifier =
            "475dda83-9447-4626-9cf1-ecc4ddbe5bbd".parse()?;
        let kdf_nonce = KdfNonce::random()?;
        let metadata = BackupMetadata::builder()
            .backup_scheme(BackupScheme::V1)
            .backup_version(16)
            .device_id(device_id.clone())
            .device_name(device_name)
            .kdf_nonce(&kdf_nonce)
            .build();

        let file_name = metadata.backup_file_name();
        let meta_from_file_name: MetadataFromFileName = file_name.parse()?;

        assert_eq!(meta_from_file_name.backup_version, metadata.backup_version);
        assert_eq!(meta_from_file_name.device_id, metadata.device_id);

        Ok(())
    }
}
