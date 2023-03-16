// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

mod backup_error;
mod backup_scheme;
mod backup_storage;
mod create;
mod metadata;
mod restore;
mod setup;

// File names inside the backup zip
pub(in crate::backup) const ENCRYPTED_BACKUP_FILE_NAME: &str = "backup.sqlite3.encrypted";

pub(in crate::backup) const METADATA_FILE_NAME: &str = "metadata.json";

pub use backup_error::BackupError;
pub use backup_scheme::BackupScheme;
#[cfg(test)]
pub use backup_storage::tmp_backup_storage::TmpBackupStorage;
pub use backup_storage::BackupStorageI;
pub use create::create_backup;
pub use metadata::{last_uploaded_backup, BackupMetadata, BackupVersion};
pub use restore::{find_latest_backup, restore_backup, BackupRestoreData};
pub use setup::{
    disable_backup, display_backup_password, is_backup_enabled, set_up_or_rotate_backup,
};

#[cfg(test)]
mod tests {
    use std::{io::Write, sync::Arc};

    use anyhow::Result;
    use tempfile::NamedTempFile;

    use super::*;
    use crate::{
        app_core::tests::{CoreResourcesMock, TmpCoreDir},
        backup::{
            backup_scheme::BackupScheme,
            create::db_backup,
            metadata::{get_backup_file_name, BackupVersion, MetadataFromFileName},
            restore::{
                backup_metadata_from_zip, find_latest_backup_inner, restore_backup_inner,
                RestoreWorkDir,
            },
            setup::rollback_enable_backup,
        },
        db::{
            data_migrations, models as m, schema_migrations::run_migrations,
            ConnectionPool,
        },
        device::{DeviceIdentifier, DeviceName, OperatingSystem},
        encryption::{KdfSecret, Keychain},
        protocols::eth,
        resources::CoreResourcesI,
        utils::{path_to_string, tmp_file, unix_timestamp},
        CoreArgs,
    };

    struct BackupTest {
        pub resources: Arc<CoreResourcesMock>,
    }

    impl BackupTest {
        fn new() -> Result<Self> {
            let tmp_dir = TmpCoreDir::new()?;
            let resources = Arc::new(CoreResourcesMock::new(tmp_dir, false)?);

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

        fn backup_storage(&self) -> &dyn BackupStorageI {
            self.resources.backup_storage()
        }

        fn setup_or_rotate_backup(&self) -> Result<()> {
            set_up_or_rotate_backup(self.resources.as_ref())?;
            Ok(())
        }

        fn backup_password(&self) -> Result<String> {
            let res = display_backup_password(self.resources.keychain())?;
            Ok(res)
        }

        fn create_backup(&self) -> Result<BackupMetadata> {
            let metadata = create_backup(self.resources.as_ref())?;
            Ok(metadata)
        }

        fn create_backup_without_deleting_outdated(&self) -> Result<BackupMetadata> {
            let metadata = db_backup(self.resources.as_ref())?;
            Ok(metadata)
        }

        fn backup_versions_in_dir(&self) -> Result<Vec<BackupVersion>> {
            let mut res: Vec<BackupVersion> = Default::default();
            let backup_storage = self.backup_storage();
            for file_name in backup_storage.list_backup_file_names() {
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
            let db_file_path = self.restore_to.path().to_str().unwrap().to_string();
            let core_args = CoreArgs {
                device_id: self.resources.device_id().to_string(),
                device_name: self.resources.device_name().to_string(),
                // This is not used for restore
                cache_dir: "".into(),
                db_file_path,
            };

            let backup_metadata = restore_backup_inner(
                core_args,
                self.resources.backup_storage(),
                metadata.backup_file_name(),
                self.resources.keychain(),
                password,
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
                let encrypted_secret_key =
                    m::Address::fetch_encrypted_signing_key(&mut tx_conn, &address_id)?;
                // Uses SK-KEK to decrypt
                encrypted_secret_key.decrypt(self.resources.keychain())
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
        let zero_backup_version: BackupVersion = 0.try_into()?;
        assert!(initial_backup_version > zero_backup_version);

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
        rollback_enable_backup(
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
        rollback_enable_backup(
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
    fn can_disable_backups() -> Result<()> {
        let backup = BackupTest::new()?;

        backup.setup_or_rotate_backup()?;
        let backup_metadata = backup.create_backup()?;

        disable_backup(backup.resources.as_ref())?;

        let backup_enabled = is_backup_enabled(backup.resources.connection_pool())?;
        assert!(!backup_enabled);
        let res = find_latest_backup_inner(backup.backup_storage())?;
        assert!(res.is_none());

        let mut conn = backup.resources.connection_pool().connection()?;
        let backup_version = m::LocalSettings::fetch_backup_version(&mut conn)?;
        // Backup version shouldn't be reset after disabling as it should be monotonously
        // increasing.
        assert_eq!(backup_version, backup_metadata.backup_version);

        Ok(())
    }

    #[test]
    fn can_enable_after_disable_backups() -> Result<()> {
        let backup = BackupTest::new()?;

        backup.setup_or_rotate_backup()?;

        disable_backup(backup.resources.as_ref())?;

        backup.setup_or_rotate_backup()?;
        let password = backup.backup_password()?;

        let backup_metadata = backup.create_backup()?;

        let restore = RestoreTest::new(backup)?;
        restore.verify(&password, &backup_metadata)?;

        Ok(())
    }

    #[test]
    fn can_disable_backups_if_not_enabled() -> Result<()> {
        let backup = BackupTest::new()?;

        disable_backup(backup.resources.as_ref())?;

        Ok(())
    }

    #[test]
    fn empty_dir_ok_for_finding_restorable() -> Result<()> {
        let backup = BackupTest::new()?;
        let res = find_latest_backup_inner(backup.backup_storage())?;
        assert!(res.is_none());
        Ok(())
    }

    #[test]
    fn finds_restorable() -> Result<()> {
        let backup = BackupTest::new()?;
        backup.setup_or_rotate_backup()?;
        let _ = backup.create_backup_without_deleting_outdated()?;
        let metadata = backup.create_backup_without_deleting_outdated()?;

        // Make sure it can handle an unexpected file name in the directory
        let mut file = tmp_file()?;
        file.write_all(b"some random data")?;
        file.flush()?;
        let backup_storage = backup.backup_storage();
        backup_storage
            .copy_to_storage("some-random-file.zip".into(), path_to_string(file.path())?);

        let res = find_latest_backup_inner(backup.backup_storage())?
            .expect("there is a restorable backup");
        let device_name: DeviceName = res.device_name.parse()?;
        assert_eq!(&metadata.device_name, &device_name);
        assert_eq!(&metadata.timestamp, &res.timestamp);
        assert_eq!(&metadata.backup_file_name(), &res.backup_file_name);

        let work_dir = RestoreWorkDir::new(&metadata.backup_file_name())?;
        assert!(backup_storage.copy_from_storage(
            res.backup_file_name.clone(),
            work_dir.zip_path_string()?
        ));
        let meta_from_zip = backup_metadata_from_zip(work_dir.zip_path())?;
        assert_eq!(meta_from_zip, metadata);
        assert_eq!(&meta_from_zip.backup_file_name(), &res.backup_file_name);

        Ok(())
    }

    #[test]
    fn device_id_from_filename_ok() -> Result<()> {
        let os: OperatingSystem = Default::default();
        let device_id: DeviceIdentifier =
            "475dda83-9447-4626-9cf1-ecc4ddbe5bbd".parse()?;
        let backup_version: BackupVersion = 16.try_into()?;
        let timestamp = unix_timestamp();

        let file_name = get_backup_file_name(
            BackupScheme::V1,
            &os,
            timestamp,
            &device_id,
            backup_version,
        );
        let meta_from_file_name: MetadataFromFileName = file_name.parse()?;

        assert_eq!(&meta_from_file_name.os, &os);
        assert_eq!(&meta_from_file_name.device_id, &device_id);
        assert_eq!(meta_from_file_name.backup_version, backup_version);
        assert_eq!(meta_from_file_name.timestamp, timestamp);

        Ok(())
    }
}
