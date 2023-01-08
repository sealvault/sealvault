// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{path::Path, str::FromStr};

use crate::{
    backup::{metadata::MetadataFromFileName, BackupError},
    db::{models as m, ConnectionPool, ExclusiveTxConnection},
    device::DeviceIdentifier,
    encryption::{
        BackupPassword, DataEncryptionKey, KdfNonce, KdfSecret, KeyEncryptionKey,
        KeyName, Keychain, RootBackupKey,
    },
    resources::CoreResourcesI,
    Error,
};

/// Set up backup keys for the user and return the backup password that can be displayed to the
/// user. Calling the function again will rotate the password and associated keys.
pub fn set_up_or_rotate_backup(resources: &dyn CoreResourcesI) -> Result<(), Error> {
    // In an exclusive transaction to prevent running in parallel and potentially ending up with
    // mixed up keychain items.
    let res = resources
        .connection_pool()
        .exclusive_transaction(|mut tx_conn| {
            let kdf_nonce = setup_or_rotate_keys_for_backup(
                resources.keychain(),
                resources.device_id(),
                &mut tx_conn,
            )?;

            enable_backups_in_db(&mut tx_conn, &kdf_nonce)?;

            Ok(())
        });

    // Rollback on error
    if res.is_err() {
        disable_backup(resources)?;
    }

    res
}

pub fn display_backup_password(keychain: &Keychain) -> Result<String, Error> {
    let pwd = BackupPassword::from_keychain(keychain)?;
    Ok(pwd.display_to_user())
}

pub fn is_backup_enabled(connection_pool: &ConnectionPool) -> Result<bool, Error> {
    let mut conn = connection_pool.connection()?;
    m::LocalSettings::fetch_backup_enabled(&mut conn)
}

fn setup_or_rotate_keys_for_backup(
    keychain: &Keychain,
    device_identifier: &DeviceIdentifier,
    tx_conn: &mut ExclusiveTxConnection,
) -> Result<KdfNonce, Error> {
    // Create new backup password
    // KDF secret should be first to abort if something's wrong with keychain sync which is the
    // most likely failure scenario.
    let kdf_secret = KdfSecret::setup_or_rotate(keychain, device_identifier)?;
    let backup_password = BackupPassword::setup_or_rotate(keychain)?;
    let kdf_nonce: KdfNonce = KdfNonce::random()?;

    let root_backup_key =
        RootBackupKey::derive_from(&backup_password, &kdf_secret, &kdf_nonce)?;

    let db_backup_dek = root_backup_key.derive_db_backup_dek()?;
    db_backup_dek.upsert_to_local_keychain(keychain)?;

    let sk_backup_kek = root_backup_key.derive_sk_backup_kek()?;
    sk_backup_kek.upsert_to_local_keychain(keychain)?;
    let sk_backup_kek = KeyEncryptionKey::sk_backup_kek(keychain)?;

    let sk_kek = KeyEncryptionKey::sk_kek(keychain)?;

    // Fetch secret key data encryption key (SK-DEK) from DB and decrypt it with secret key
    // encryption key (SK-KEK) from local keychain.
    let (sk_dek_id, sk_dek) = m::DataEncryptionKey::fetch_dek(
        tx_conn.as_mut(),
        KeyName::SkDataEncryptionKey,
        &sk_kek,
    )?;

    // Encrypt SK-DEK with the secret key backup encryption key and save the encrypted SK-DEK in
    // the database.
    let encrypted_sk_dek = sk_dek.to_encrypted(&sk_backup_kek)?;
    let maybe_sk_dek_backup_id = m::LocalEncryptedDek::fetch_id(
        tx_conn.as_mut(),
        &sk_dek_id,
        sk_backup_kek.name(),
    )?;
    if let Some(sk_dek_backup_id) = maybe_sk_dek_backup_id {
        m::LocalEncryptedDek::set_encrypted_dek(
            tx_conn.as_mut(),
            sk_dek_backup_id,
            &encrypted_sk_dek,
        )?;
    } else {
        m::NewLocalEncryptedDek::builder()
            .dek_id(&sk_dek_id)
            .encrypted_dek(&encrypted_sk_dek)
            .kek_name(sk_backup_kek.name())
            .build()
            .insert(tx_conn.as_mut())?;
    }

    Ok(kdf_nonce)
}

fn enable_backups_in_db(
    tx_conn: &mut ExclusiveTxConnection,
    kdf_nonce: &KdfNonce,
) -> Result<(), Error> {
    // Update timestamps
    m::LocalSettings::set_backup_kdf_nonce(tx_conn.as_mut(), Some(kdf_nonce))?;
    m::LocalSettings::update_backup_password_timestamp(tx_conn.as_mut())?;
    // Reset user viewed password
    m::LocalSettings::set_backup_enabled(tx_conn.as_mut(), true)?;
    Ok(())
}

/// Disable backups in DB, delete keys from keychain and delete backups created on this device if
/// any.
pub fn disable_backup(resources: &dyn CoreResourcesI) -> Result<(), Error> {
    rollback_enable_backup(
        resources.connection_pool(),
        resources.keychain(),
        resources.device_id(),
    )?;

    // Delete backups that were created on this device.
    delete_backups_for_device(resources)?;

    Ok(())
}

/// Disable backups in DB and delete keys from keychain
pub(in crate::backup) fn rollback_enable_backup(
    connection_pool: &ConnectionPool,
    keychain: &Keychain,
    device_identifier: &DeviceIdentifier,
) -> Result<(), Error> {
    // First make sure we disable backups as keychain might be in inconsistent state.
    // Rolling back the changes from the transaction is not enough, because backups might have
    // been enabled prior.
    connection_pool.deferred_transaction(|mut tx_conn| {
        m::LocalSettings::disable_backups(&mut tx_conn)?;
        Ok(())
    })?;
    // Try to clean up keychain items. The application works correctly even if they're not
    // all successfully cleaned up.
    remove_keys_for_backup(keychain, device_identifier);
    Ok(())
}

pub fn remove_keys_for_backup(keychain: &Keychain, device_identifier: &DeviceIdentifier) {
    let _ = KdfSecret::delete_from_keychain_if_exists(keychain, device_identifier);
    let _ = BackupPassword::delete_from_keychain_if_exists(keychain);
    let _ = KeyEncryptionKey::delete_from_keychain_if_exists(
        keychain,
        KeyName::SkBackupKeyEncryptionKey,
    );
    let _ = DataEncryptionKey::delete_from_keychain_if_exists(
        keychain,
        KeyName::DbBackupDataEncryptionKey,
    );
}

fn delete_backups_for_device(resources: &dyn CoreResourcesI) -> Result<(), BackupError> {
    let device_id = resources.device_id();
    let backup_storage = resources.backup_storage();

    let mut did_err = false;
    for backup_file_name in backup_storage.list_backup_file_names() {
        if let Ok(meta_from_file_name) = MetadataFromFileName::from_str(&backup_file_name)
        {
            if &meta_from_file_name.device_id == device_id {
                let success = backup_storage.delete_backup(backup_file_name);
                if !success {
                    // Don't break on first error, in order to try to delete as many as possible.
                    did_err = true;
                }
            }
        }
    }
    if did_err {
        Err(BackupError::FailedToDeleteBackup)
    } else {
        Ok(())
    }
}

/// Set up SK-KEK if we're on new device as it's not on the local keychain. Rotate if the app is
/// reinstalled on same device for hygiene.
/// It's possible that SK-KEK already exists when reinstalling on same device since iOS Keychain
/// items are not deleted when the app is deleted.
pub(in crate::backup) fn set_up_or_rotate_sk_kek(
    keychain: &Keychain,
    sk_backup_kek: &KeyEncryptionKey,
    db_path: &Path,
) -> Result<ConnectionPool, Error> {
    let backup_cp = backup_connection_pool(db_path)?;
    backup_cp.exclusive_transaction(|mut tx_conn| {
        // Fetch the secret key data encryption key (SK-DEK) from the database and decrypt it with the backup key encryption key
        let (dek_id, sk_dek) = m::DataEncryptionKey::fetch_dek(tx_conn.as_mut(), KeyName::SkDataEncryptionKey, sk_backup_kek)?;
        // Create a new secret key encryption key (SK-KEK)
        let sk_kek = KeyEncryptionKey::random(KeyName::SkKeyEncryptionKey)?;
        // Encrypt the SK-DEK with the new SK-KEK
        let encrypted_sk_dek = sk_dek.to_encrypted(&sk_kek)?;
        // Update the encrypted SK-DEK in the db to the one newly encrypted with new SK-KEK.
        // The local encrypted SK-DEK with SK-KEK from previous device is assumed to exist in the
        // backup, since it's created in the first data migration, ergo all backups should have it.
        let sk_dek_id = m::LocalEncryptedDek::fetch_id(tx_conn.as_mut(), &dek_id, sk_kek.name())?.ok_or_else(|| Error::Fatal {
            error: "Local encrypted SK-DEK with SK-KEK is assumed to exist when calling `rotate_sk_kek`".into()
        })?;
        m::LocalEncryptedDek::set_encrypted_dek(tx_conn.as_mut(), sk_dek_id, &encrypted_sk_dek)?;
        // Save the new SK-KEK to the keychain.
        sk_kek.upsert_to_local_keychain(keychain)
    })?;
    Ok(backup_cp)
}

pub(in crate::backup) fn backup_connection_pool(
    backup_path: &Path,
) -> Result<ConnectionPool, Error> {
    let backup_path = backup_path.to_str().ok_or_else(|| Error::Fatal {
        error: "Failed to convert backup path to utf-8".into(),
    })?;
    ConnectionPool::new(backup_path)
}
