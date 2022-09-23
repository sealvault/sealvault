// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::config;

use crate::db::{models as m, DeferredTxConnection, ExclusiveTxConnection};
use crate::encryption::Keychain;
use crate::encryption::{DataEncryptionKey, KeyEncryptionKey};

use crate::Error;

trait Migration {
    fn version() -> &'static str;
    fn description() -> &'static str;
    fn run(connection: ExclusiveTxConnection, keychain: &Keychain) -> Result<(), Error>;
}

struct MigrationV0 {}

impl Migration for MigrationV0 {
    fn version() -> &'static str {
        "v0"
    }

    fn description() -> &'static str {
        "Creates SK-KEK, SK-DEK and Default account with an Ethereum/Polygon PoS wallet address."
    }

    fn run(tx_conn: ExclusiveTxConnection, keychain: &Keychain) -> Result<(), Error> {
        // We take an ExclsuvieTxConnection as argument, because this method should be run in an
        // exclusive transaction, but called function can be ran in deferred transactions as well.
        let mut tx_conn: DeferredTxConnection = tx_conn.into();

        // Generate SK-DEK and SK-KEK
        let sk_dek = DataEncryptionKey::random(config::SK_DEK_NAME.to_string())?;
        let sk_kek = KeyEncryptionKey::random(config::SK_KEK_NAME.to_string())?;
        // TODO delete if tx fails, otherwise it won't be able to run again
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
            m::Account::create_eth_account(&mut tx_conn, keychain, &account_params)?;

        m::LocalSettings::create(tx_conn.as_mut(), &account_id)?;

        // Record data migration
        m::NewDataMigration::builder()
            .version(Self::version())
            .description(Self::description())
            .build()
            .insert(tx_conn.as_mut())?;

        Ok(())
    }
}

pub fn run_all(
    mut tx_conn: ExclusiveTxConnection,
    keychain: &Keychain,
) -> Result<(), Error> {
    if m::DataMigration::list_all(tx_conn.as_mut())?.is_empty() {
        MigrationV0::run(tx_conn, keychain)
    } else {
        Ok(())
    }
}
