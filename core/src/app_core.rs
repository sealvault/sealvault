// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashSet, fmt::Debug, sync::Arc};

use rand::seq::IteratorRandom;
use typed_builder::TypedBuilder;

use crate::{
    assets::{list_profile_pics, load_profile_pic},
    async_runtime as rt, backup,
    backup::{BackupError, BackupStorageI},
    db::{
        data_migrations, models as m, schema_migrations::run_migrations, ConnectionPool,
    },
    device::{DeviceIdentifier, DeviceName},
    dto,
    encryption::Keychain,
    error::Error,
    http_client::HttpClient,
    in_page_provider,
    in_page_provider::{InPageProvider, InPageRequestContextI},
    protocols::eth,
    public_suffix_list::PublicSuffixList,
    resources::{CoreResources, CoreResourcesI},
    ui_callback::TokenTransferResult,
    CoreError, CoreUICallbackI, DappApprovalParams,
};

/// Provides cross-platform key and transaction management.
/// Exposed to host language via FFI.
/// The methods take ownership of arguments, because FFI needs owning interfaces.
/// All members are `Send + Sync + 'static`.
/// No async interfaces, because concurrency is managed by the host languages.
#[derive(Debug)]
pub struct AppCore {
    resources: Arc<dyn CoreResourcesI>,
}

impl AppCore {
    // UI callbacks cannot be part of the args struct, because Uniffi expects it to be hashable
    // then.
    pub fn new(
        args: CoreArgs,
        backup_storage: Box<dyn BackupStorageI>,
        ui_callbacks: Box<dyn CoreUICallbackI>,
    ) -> Result<Self, CoreError> {
        let rpc_manager = Box::new(eth::RpcManager::new());
        let connection_pool = ConnectionPool::new(&args.db_file_path)?;
        let keychain = Keychain::new();
        let public_suffix_list = PublicSuffixList::new()?;
        let http_client = HttpClient::new(args.cache_dir);

        let CoreArgs {
            device_name,
            device_id,
            ..
        } = args;
        let device_id: DeviceIdentifier = device_id.try_into()?;
        let device_name: DeviceName = device_name.try_into()?;

        let resources = CoreResources::builder()
            .ui_callbacks(ui_callbacks)
            .rpc_manager(rpc_manager)
            .connection_pool(connection_pool)
            .keychain(keychain)
            .http_client(http_client)
            .public_suffix_list(public_suffix_list)
            .backup_storage(backup_storage)
            .device_id(device_id)
            .device_name(device_name)
            .build();

        Self::new_with_overrides(Arc::new(resources))
    }

    fn connection_pool(&self) -> &ConnectionPool {
        self.resources.connection_pool()
    }

    fn keychain(&self) -> &Keychain {
        self.resources.keychain()
    }

    fn rpc_manager(&self) -> &dyn eth::RpcManagerI {
        self.resources.rpc_manager()
    }

    fn assembler(&self) -> dto::Assembler {
        dto::Assembler::new(self.resources.clone())
    }

    /// Let us mock functionality. Not exposed through FFI.
    pub fn new_with_overrides(
        resources: Arc<dyn CoreResourcesI>,
    ) -> Result<Self, CoreError> {
        // Run DB schema migrations and data migrations that haven't been applied yet.
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

        Ok(AppCore { resources })
    }

    /// Method called by the UI when the application enters the background.
    pub fn on_background(&self) -> Result<(), CoreError> {
        if self.is_backup_enabled()? {
            backup::create_backup(self.resources.as_ref())?;
        }
        Ok(())
    }

    pub fn enable_backup(&self) -> Result<(), BackupError> {
        backup::set_up_or_rotate_backup(self.resources.as_ref())?;
        // Check if we can create backups after enabling them.
        match backup::create_backup(self.resources.as_ref()) {
            Ok(_) => Ok(()),
            Err(error) => {
                // If we can't create backups, disable.
                self.disable_backup()?;
                Err(error)
            }
        }
    }

    pub fn disable_backup(&self) -> Result<(), CoreError> {
        backup::disable_backup(self.resources.as_ref())?;
        Ok(())
    }

    /// Get the last backup time if any as unix timestamp. Returns None if there are no backups or
    /// the last backup hasn't been uploaded yet to cloud storage.
    pub fn last_uploaded_backup(&self) -> Result<Option<i64>, CoreError> {
        let result = backup::last_uploaded_backup(self.resources.as_ref())?;
        Ok(result)
    }

    pub fn display_backup_password(&self) -> Result<String, CoreError> {
        let res = backup::display_backup_password(self.keychain())?;
        Ok(res)
    }

    pub fn is_backup_enabled(&self) -> Result<bool, CoreError> {
        let res = backup::is_backup_enabled(self.connection_pool())?;
        Ok(res)
    }

    pub fn list_profiles(&self) -> Result<Vec<dto::CoreProfile>, CoreError> {
        let res = self.assembler().assemble_profiles()?;
        Ok(res)
    }

    pub fn active_profile_id(&self) -> Result<String, CoreError> {
        let mut conn = self.connection_pool().connection()?;
        let res = m::LocalSettings::fetch_active_profile_id(&mut conn)?;
        Ok(res)
    }

    pub fn set_active_profile_id(&self, profile_id: String) -> Result<(), CoreError> {
        let mut conn = self.connection_pool().connection()?;
        m::LocalSettings::set_active_profile_id(&mut conn, &profile_id)?;
        Ok(())
    }

    pub fn create_profile(
        &self,
        name: String,
        bundled_picture_name: String,
    ) -> Result<(), CoreError> {
        let name: m::ProfileName = name.try_into()?;
        self.connection_pool().deferred_transaction(|mut tx_conn| {
            m::Profile::create_eth_profile(
                &mut tx_conn,
                self.keychain(),
                &name,
                &bundled_picture_name,
            )?;
            Ok(())
        })?;
        Ok(())
    }

    /// Return the name of a random bundled profile picture that can be used for a new profile.
    /// Returns none if there are no unused.
    pub fn random_bundled_profile_picture(&self) -> Result<Option<String>, CoreError> {
        let mut conn = self.connection_pool().connection()?;
        let taken_names: HashSet<String> = m::ProfilePicture::list_names(&mut conn)?
            .into_iter()
            .collect();
        let bundled_names: HashSet<String> = list_profile_pics().into_iter().collect();

        let res = bundled_names
            .difference(&taken_names)
            .choose(&mut rand::thread_rng());

        Ok(res.cloned())
    }

    pub fn fetch_bundled_profile_picture(
        &self,
        picture_name: String,
    ) -> Result<Vec<u8>, CoreError> {
        let picture = load_profile_pic(&picture_name)?;
        Ok(picture)
    }

    pub fn native_token_for_address(
        &self,
        address_id: String,
    ) -> Result<dto::CoreToken, CoreError> {
        let res = self.assembler().native_token_for_address(&address_id)?;
        Ok(res)
    }

    pub fn fungible_tokens_for_address(
        &self,
        address_id: String,
    ) -> Result<Vec<dto::CoreToken>, CoreError> {
        let res = self.assembler().fungible_tokens_for_address(&address_id)?;
        Ok(res)
    }

    pub fn get_in_page_script(
        &self,
        rpc_provider_name: String,
        request_handler_name: String,
    ) -> Result<String, CoreError> {
        let res = in_page_provider::load_in_page_provider_script(
            &rpc_provider_name,
            &request_handler_name,
        )?;
        Ok(res)
    }

    pub fn in_page_request(
        &self,
        context: Box<dyn InPageRequestContextI>,
        raw_request: String,
    ) -> Result<(), CoreError> {
        let resources = self.resources.clone();
        let provider = InPageProvider::new(resources, context)?;
        provider.in_page_request(raw_request);
        Ok(())
    }

    pub fn user_approved_dapp(
        &self,
        context: Box<dyn InPageRequestContextI>,
        dapp_approval: DappApprovalParams,
    ) -> Result<(), CoreError> {
        let resources = self.resources.clone();
        let provider = InPageProvider::new(resources, context)?;
        provider.user_approved_dapp(dapp_approval);
        Ok(())
    }

    pub fn user_rejected_dapp(
        &self,
        context: Box<dyn InPageRequestContextI>,
        dapp_approval: DappApprovalParams,
    ) -> Result<(), CoreError> {
        let resources = self.resources.clone();
        let provider = InPageProvider::new(resources, context)?;
        provider.user_rejected_dapp(dapp_approval);
        Ok(())
    }

    /// Transfer native token on an Ethereum protocol network.
    pub fn eth_transfer_native_token(
        &self,
        args: EthTransferNativeTokenArgs,
    ) -> Result<(), CoreError> {
        let signing_key = fetch_eth_signing_key_for_transfer(
            &*self.resources,
            &args.from_address_id,
            &args.to_checksum_address,
        )?;

        let amount = eth::NativeTokenAmount::new_from_decimal(
            signing_key.chain_id,
            &args.amount_decimal,
        )?;
        let rpc_provider = self.rpc_manager().eth_api_provider(signing_key.chain_id);
        let tx_hash_res = rpc_provider.transfer_native_token(
            &signing_key,
            &args.to_checksum_address,
            &amount,
        );

        let resources = self.resources.clone();
        rt::spawn_blocking(move || {
            let res = token_transfer_callbacks(resources, args.into(), tx_hash_res);
            if let Some(err) = res.err() {
                log::error!(
                    "Failed to call native token transfer callbacks due to error: {err:?}"
                )
            }
        });

        Ok(())
    }

    /// Transfer fungible native token on an Ethereum protocol network.
    /// Returns the tx hash that can be used to poll for the result.
    pub fn eth_transfer_fungible_token(
        &self,
        args: EthTransferFungibleTokenArgs,
    ) -> Result<(), CoreError> {
        // TODO we use contract address as token id for now, but it should be chain specific
        let contract_address = &args.token_id;
        let signing_key = fetch_eth_signing_key_for_transfer(
            &*self.resources,
            &args.from_address_id,
            &args.to_checksum_address,
        )?;

        let rpc_provider = self.rpc_manager().eth_api_provider(signing_key.chain_id);
        let tx_hash_res = rpc_provider.transfer_fungible_token(
            &signing_key,
            &args.to_checksum_address,
            &args.amount_decimal,
            contract_address,
        );

        let resources = self.resources.clone();
        rt::spawn_blocking(move || {
            let res = token_transfer_callbacks(resources, args.into(), tx_hash_res);
            if let Some(err) = res.err() {
                log::error!(
                    "Failed to call native token transfer callbacks due to error: {err:?}"
                )
            }
        });

        Ok(())
    }

    /// List supported Ethereum chains.
    pub fn list_eth_chains(&self) -> Vec<dto::CoreEthChain> {
        self.assembler().list_eth_chains()
    }

    /// Add a supported Ethereum chain to an address. The operation is idempotent.
    pub fn add_eth_chain(
        &self,
        chain_id: u64,
        address_id: String,
    ) -> Result<(), CoreError> {
        let chain_id: eth::ChainId = chain_id.try_into()?;
        let _ = self
            .connection_pool()
            .deferred_transaction(move |mut tx_conn| {
                m::Address::add_eth_chain(&mut tx_conn, &address_id, chain_id)
            })?;
        Ok(())
    }

    /// Change the address to connect with to a dapp.
    /// Assumes there is already a key for the dapp in the profile.
    pub fn eth_change_dapp_chain(
        &self,
        args: EthChangeDappChainArgs,
    ) -> Result<(), CoreError> {
        let new_chain_id: eth::ChainId = args.new_chain_id.try_into()?;
        self.connection_pool()
            .deferred_transaction(move |mut tx_conn| {
                let params = m::NewDappSessionParams::builder()
                    .profile_id(&args.profile_id)
                    .dapp_id(&args.dapp_id)
                    .chain_id(new_chain_id)
                    .build();
                let session = m::LocalDappSession::create_eth_session_if_not_exists(
                    &mut tx_conn,
                    &params,
                )?;
                session.change_eth_chain(&mut tx_conn, new_chain_id)?;
                Ok(())
            })?;
        Ok(())
    }

    /// List the ids of the top dapps used by the user.
    pub fn top_dapps(&self, limit: u32) -> Result<Vec<String>, CoreError> {
        let res = self.connection_pool().deferred_transaction(|mut tx_conn| {
            // Prefer dapps that have sessions on this device.
            let mut session_dapp_ids =
                m::LocalDappSession::list_dapp_ids_desc(tx_conn.as_mut(), limit)?;
            // u32 is guaranteed to fit into usize on all supported platforms
            if session_dapp_ids.len() < limit as usize {
                // Fall back to dapps that haven't been connected on this device yet.
                let dapp_ids = m::Dapp::list_dapp_ids_desc(tx_conn.as_mut(), limit)?;
                session_dapp_ids.extend(dapp_ids)
            }
            Ok(session_dapp_ids)
        })?;

        Ok(res)
    }
}

#[derive(Debug)]
pub struct CoreArgs {
    pub device_id: String,
    pub device_name: String,
    pub cache_dir: String,
    pub db_file_path: String,
}

#[derive(Debug, Clone, TypedBuilder)]
pub struct EthTransferNativeTokenArgs {
    pub from_address_id: String,
    pub to_checksum_address: String,
    pub amount_decimal: String,
}

#[derive(Debug, Clone, TypedBuilder)]
pub struct EthTransferFungibleTokenArgs {
    pub from_address_id: String,
    pub to_checksum_address: String,
    pub amount_decimal: String,
    pub token_id: String,
}

#[derive(Debug, Clone, TypedBuilder)]
pub struct EthChangeDappChainArgs {
    pub profile_id: String,
    pub dapp_id: String,
    pub new_chain_id: u64,
}

#[derive(Debug, Clone)]
struct EthTokenTransferCallbackArgs {
    pub from_address_id: String,
    pub to_checksum_address: String,
    pub amount_decimal: String,
    pub token_id: Option<String>,
}

impl From<EthTransferNativeTokenArgs> for EthTokenTransferCallbackArgs {
    fn from(value: EthTransferNativeTokenArgs) -> Self {
        let EthTransferNativeTokenArgs {
            from_address_id,
            to_checksum_address,
            amount_decimal,
        } = value;
        EthTokenTransferCallbackArgs {
            from_address_id,
            to_checksum_address,
            amount_decimal,
            token_id: None,
        }
    }
}

impl From<EthTransferFungibleTokenArgs> for EthTokenTransferCallbackArgs {
    fn from(value: EthTransferFungibleTokenArgs) -> Self {
        let EthTransferFungibleTokenArgs {
            from_address_id,
            to_checksum_address,
            amount_decimal,
            token_id,
        } = value;
        EthTokenTransferCallbackArgs {
            from_address_id,
            to_checksum_address,
            amount_decimal,
            token_id: Some(token_id),
        }
    }
}

fn fetch_eth_signing_key_for_transfer(
    resources: &dyn CoreResourcesI,
    from_address_id: &str,
    to_checksum_address: &str,
) -> Result<eth::SigningKey, Error> {
    let signing_key = resources.connection_pool().deferred_transaction(
        |mut tx_conn| {
            // Returns NotFoundError if the address is not in the db.
            let from_profile_id =
                m::Address::fetch_profile_id(tx_conn.as_mut(), from_address_id)?;
            let maybe_to_profile_id = m::Address::fetch_profile_id_for_eth_address(
                tx_conn.as_mut(),
                to_checksum_address,
            )?;

            // See privacy in developer docs fore more.
            if maybe_to_profile_id.is_some()
                && Some(from_profile_id) != maybe_to_profile_id
            {
                return Err(Error::User {
                    explanation: "Cannot transfer between profiles for privacy reasons."
                        .into(),
                })?;
            }

            m::Address::fetch_eth_signing_key(
                &mut tx_conn,
                resources.keychain(),
                from_address_id,
            )
        },
    )?;
    Ok(signing_key)
}

fn token_transfer_callbacks(
    resources: Arc<dyn CoreResourcesI>,
    args: EthTokenTransferCallbackArgs,
    tx_hash_res: Result<ethers::types::H256, Error>,
) -> Result<(), Error> {
    let (chain_id, mut transfer_res) =
        build_partial_token_transfer_result(resources.clone(), args)?;
    match tx_hash_res {
        Ok(tx_hash) => {
            let sent_res = transfer_res.clone();
            resources.ui_callbacks().sent_token_transfer(sent_res);

            let rpc_provider = resources.rpc_manager().eth_api_provider(chain_id);
            let confirmation = rpc_provider.wait_for_confirmation(tx_hash);
            match confirmation {
                Ok(tx_hash_str) => {
                    let explorer_url = eth::explorer::tx_url(chain_id, &tx_hash_str)?;
                    transfer_res.explorer_url = Some(explorer_url.to_string());
                    resources.ui_callbacks().token_transfer_result(transfer_res);
                }
                Err(err) => handle_token_callback_error(resources, transfer_res, err),
            }
        }
        Err(err) => handle_token_callback_error(resources, transfer_res, err),
    };
    Ok(())
}

fn build_partial_token_transfer_result(
    resources: Arc<dyn CoreResourcesI>,
    args: EthTokenTransferCallbackArgs,
) -> Result<(eth::ChainId, TokenTransferResult), Error> {
    let EthTokenTransferCallbackArgs {
        amount_decimal,
        from_address_id,
        to_checksum_address,
        token_id,
    } = args;
    let (chain_id, to_display_name) =
        resources
            .connection_pool()
            .deferred_transaction(move |mut tx_conn| {
                let chain_id =
                    m::Address::fetch_eth_chain_id(tx_conn.as_mut(), &from_address_id)?;
                let maybe_to_id = m::Address::fetch_id_by_checksum_address(
                    tx_conn.as_mut(),
                    &to_checksum_address,
                )?;
                let to_display_name = if let Some(to_id) = maybe_to_id {
                    if m::Address::is_profile_wallet(tx_conn.as_mut(), &to_id)? {
                        let profile_name =
                            m::Address::fetch_profile_name(tx_conn.as_mut(), &to_id)?;
                        Ok(format!("{profile_name} Profile Wallet"))
                    } else if let Some(dapp_identifier) =
                        m::Address::dapp_identifier(tx_conn.as_mut(), &to_id)?
                    {
                        Ok(dapp_identifier)
                    } else {
                        Err(Error::Fatal {
                            error: format!(
                                "Address id {to_id} is neither wallet nor dapp address"
                            ),
                        })
                    }
                } else {
                    Ok(to_checksum_address)
                }?;
                Ok((chain_id, to_display_name))
            })?;
    let res = if let Some(contract_address) = token_id {
        let rpc = resources.rpc_manager().eth_api_provider(chain_id);
        let token_symbol = rpc.fungible_token_symbol(&contract_address)?;
        TokenTransferResult::builder()
            .amount(amount_decimal)
            .token_symbol(token_symbol)
            .chain_display_name(chain_id.display_name())
            .to_display_name(to_display_name)
            .build()
    } else {
        TokenTransferResult::builder()
            .amount(amount_decimal)
            .token_symbol(chain_id.native_token().symbol())
            .chain_display_name(chain_id.display_name())
            .to_display_name(to_display_name)
            .build()
    };
    Ok((chain_id, res))
}

fn handle_token_callback_error(
    resources: Arc<dyn CoreResourcesI>,
    mut result: TokenTransferResult,
    err: Error,
) {
    let error_message = err.message_for_ui_callback();
    result.error_message = Some(error_message);
    resources.ui_callbacks().token_transfer_result(result);
}

#[cfg(test)]
pub mod tests {

    use std::{fs, path::PathBuf, sync::RwLock, thread, time::Duration};

    use anyhow::Result;
    use strum::IntoEnumIterator;
    use tempfile::TempDir;
    use typed_builder::TypedBuilder;
    use url::Url;

    use super::*;
    use crate::{
        backup::{BackupStorageI, TmpBackupStorage},
        protocols::ChecksumAddress,
        CoreInPageCallbackI, DappAllotmentTransferResult, DappApprovalParams,
        DappSignatureResult, DappTransactionApproved, DappTransactionResult,
    };

    #[derive(Debug)]
    #[readonly::make]
    pub struct TmpCoreDir {
        // The TempDir is kept to keep it open for the lifetime of the core as the db file is
        // deleted when in the TempDir dtor is invoked.
        #[allow(dead_code)]
        pub tmp_dir: TempDir,
        pub cache_dir: PathBuf,
        pub db_file_path: String,
    }

    impl TmpCoreDir {
        pub fn new() -> Result<Self, Error> {
            let tmp_dir = tempfile::tempdir().map_err(|err| Error::Fatal {
                error: err.to_string(),
            })?;
            // Important not to use in-memory DB as Sqlite has subtle differences in in memory
            // mode.
            let db_dir = tmp_dir.path().join("db");
            let cache_dir = tmp_dir.path().join("cache");

            fs::create_dir(&db_dir).unwrap();
            fs::create_dir(&cache_dir).unwrap();

            let db_file_path = db_dir
                .join("tmp-db.sqlite3")
                .into_os_string()
                .into_string()
                .unwrap();

            Ok(Self {
                tmp_dir,
                cache_dir,
                db_file_path,
            })
        }
    }

    #[derive(Debug)]
    #[readonly::make]
    pub struct CoreResourcesMock {
        tmp_dir: TmpCoreDir,
        ui_callbacks: Box<CoreUICallbackMock>,
        connection_pool: ConnectionPool,
        keychain: Keychain,
        http_client: HttpClient,
        rpc_manager: Box<eth::AnvilRpcManager>,
        public_suffix_list: PublicSuffixList,
        backup_storage: Box<TmpBackupStorage>,
        device_id: DeviceIdentifier,
        device_name: DeviceName,
    }

    impl CoreResourcesMock {
        pub fn new(tmp_dir: TmpCoreDir, disable_backups: bool) -> Result<Self, Error> {
            let rpc_manager = Box::new(eth::AnvilRpcManager::new());
            let ui_callback_state = Arc::new(UICallbackState::new());
            let ui_callbacks =
                Box::new(CoreUICallbackMock::new(ui_callback_state.clone()));
            let connection_pool = ConnectionPool::new(&tmp_dir.db_file_path)?;
            let keychain = Keychain::new();

            let cache_dir = tmp_dir
                .cache_dir
                .clone()
                .into_os_string()
                .into_string()
                .expect("path ok");
            let http_client = HttpClient::new(cache_dir);

            let public_suffix_list = PublicSuffixList::new()?;

            let backup_storage = Box::new(TmpBackupStorage::new(!disable_backups)?);
            let device_id = "test-device-id".parse()?;
            let device_name = "test-device-name".parse()?;

            Ok(Self {
                tmp_dir,
                ui_callbacks,
                rpc_manager,
                connection_pool,
                keychain,
                http_client,
                public_suffix_list,
                backup_storage,
                device_id,
                device_name,
            })
        }

        pub fn set_keychain(&mut self, keychain: Keychain) {
            self.keychain = keychain
        }

        pub fn set_device_id(&mut self, device_id: DeviceIdentifier) {
            self.device_id = device_id
        }
    }

    impl CoreResourcesI for CoreResourcesMock {
        fn ui_callbacks(&self) -> &dyn CoreUICallbackI {
            &*self.ui_callbacks
        }

        fn connection_pool(&self) -> &ConnectionPool {
            &self.connection_pool
        }

        fn keychain(&self) -> &Keychain {
            &self.keychain
        }

        fn http_client(&self) -> &HttpClient {
            &self.http_client
        }

        fn rpc_manager(&self) -> &dyn eth::RpcManagerI {
            &*self.rpc_manager
        }

        fn public_suffix_list(&self) -> &PublicSuffixList {
            &self.public_suffix_list
        }

        fn backup_storage(&self) -> &dyn BackupStorageI {
            &*self.backup_storage
        }

        fn device_id(&self) -> &DeviceIdentifier {
            &self.device_id
        }

        fn device_name(&self) -> &DeviceName {
            &self.device_name
        }
    }

    /// Create an empty path in a temp directory for a Sqlite DB.
    pub(crate) struct TmpCore {
        pub core: Arc<AppCore>,
        ui_callback_state: Arc<UICallbackState>,
        in_page_callback_state: Arc<InPageCallbackStateMock>,
        resources: Arc<CoreResourcesMock>,
    }

    // For polling callback responses.
    // 101 ms in case a future polls at every 100ms
    const SLEEP_DURATION_MS: u64 = 101;
    const SLEEP_TIMES: u64 = 5;

    impl TmpCore {
        pub fn new() -> Result<Self, CoreError> {
            Self::with_overrides(false)
        }

        pub fn with_overrides(disable_backups: bool) -> Result<Self, CoreError> {
            // Important not to use in-memory DB as Sqlite has subtle differences in in memory
            // mode.
            let tmp_dir = TmpCoreDir::new()?;

            let resources = Arc::new(CoreResourcesMock::new(tmp_dir, disable_backups)?);
            let core = Arc::new(AppCore::new_with_overrides(resources.clone())?);
            let ui_callback_state = resources.ui_callbacks.state.clone();

            let page_url = Url::parse("https://example.com").expect("static url ok");
            let in_page_callback_state =
                Arc::new(InPageCallbackStateMock::new(core.clone(), page_url));

            Ok(TmpCore {
                core,
                ui_callback_state,
                in_page_callback_state,
                resources,
            })
        }

        pub fn connection_pool(&self) -> &ConnectionPool {
            self.resources.connection_pool()
        }

        pub fn keychain(&self) -> &Keychain {
            self.resources.keychain()
        }

        pub fn data_migration_version(&self) -> Result<Option<String>, Error> {
            let mut conn = self.core.connection_pool().connection()?;
            let migrations = m::DataMigration::list_versions_sorted(&mut conn)?;
            Ok(migrations.last().map(|v| v.into()))
        }

        pub fn first_profile(&self) -> dto::CoreProfile {
            let profiles = self.core.list_profiles().expect("cannot list profiles");
            profiles.into_iter().next().expect("there is one profile")
        }

        pub fn first_profile_wallet(&self) -> dto::CoreAddress {
            let profile = self.first_profile();
            profile
                .wallets
                .into_iter()
                .next()
                .expect("there is an profile wallet")
        }

        pub fn fund_first_profile_wallet(&self, chain_id: eth::ChainId) {
            let rpc_manager = &self.resources.rpc_manager;
            let wallet = self.first_profile_wallet();
            rpc_manager.send_native_token(chain_id, &wallet.checksum_address, 10);
        }

        pub fn in_page_provider(&self) -> InPageProvider {
            let context = Box::new(InPageRequestContextMock::new(
                Default::default(),
                self.in_page_callback_state.clone(),
            ));

            InPageProvider::new(self.resources.clone(), context).expect("url valid")
        }

        pub fn in_page_provider_with_args(
            &self,
            args: InPageRequestContextMockArgs,
        ) -> InPageProvider {
            let context = Box::new(InPageRequestContextMock::new(
                args,
                self.in_page_callback_state.clone(),
            ));

            InPageProvider::new(self.resources.clone(), context).expect("url valid")
        }

        pub fn wait_for_first_in_page_response(&self) {
            for _ in 0..SLEEP_TIMES {
                thread::sleep(Duration::from_millis(SLEEP_DURATION_MS));
                // Don't hold the lock while sleeping.
                if !self.responses().is_empty() {
                    break;
                }
            }
        }

        pub fn wait_for_ui_callbacks(&self, count: usize) {
            for _ in 0..SLEEP_TIMES {
                thread::sleep(Duration::from_millis(SLEEP_DURATION_MS));
                // Don't hold the lock while sleeping.
                if self.ui_callback_state.count() == count {
                    break;
                }
            }
        }

        pub fn dapp_approval(&self) -> Option<DappApprovalParams> {
            self.in_page_callback_state
                .dapp_approval
                .read()
                .unwrap()
                // Must clone because of RwLock
                .clone()
        }

        pub fn responses(&self) -> Vec<String> {
            self.in_page_callback_state
                .responses
                .read()
                .unwrap()
                .clone()
        }

        pub fn notifications(&self) -> Vec<String> {
            self.in_page_callback_state
                .notifications
                .read()
                .unwrap()
                .clone()
        }

        pub fn sent_token_transfers(&self) -> Vec<TokenTransferResult> {
            self.ui_callback_state
                .sent_token_transfers
                .read()
                .unwrap()
                .clone()
        }

        pub fn token_transfer_results(&self) -> Vec<TokenTransferResult> {
            self.ui_callback_state
                .token_transfer_results
                .read()
                .unwrap()
                .clone()
        }

        pub fn dapp_allotment_transfer_results(
            &self,
        ) -> Vec<DappAllotmentTransferResult> {
            self.ui_callback_state
                .dapp_allotment_transfer_results
                .read()
                .unwrap()
                .clone()
        }

        pub fn dapp_tx_approvals(&self) -> Vec<DappTransactionApproved> {
            self.ui_callback_state
                .dapp_transaction_approved
                .read()
                .unwrap()
                .clone()
        }

        pub fn dapp_tx_results(&self) -> Vec<DappTransactionResult> {
            self.ui_callback_state
                .dapp_transaction_results
                .read()
                .unwrap()
                .clone()
        }

        pub fn dapp_signature_results(&self) -> Vec<DappSignatureResult> {
            self.ui_callback_state
                .dapp_signature_results
                .read()
                .unwrap()
                .clone()
        }

        pub fn dapp_url(&self) -> &Url {
            &self.in_page_callback_state.page_url
        }
    }

    #[derive(Debug, Default)]
    pub struct UICallbackState {
        sent_token_transfers: Arc<RwLock<Vec<TokenTransferResult>>>,
        token_transfer_results: Arc<RwLock<Vec<TokenTransferResult>>>,
        dapp_allotment_transfer_results: Arc<RwLock<Vec<DappAllotmentTransferResult>>>,
        dapp_signature_results: Arc<RwLock<Vec<DappSignatureResult>>>,
        dapp_transaction_approved: Arc<RwLock<Vec<DappTransactionApproved>>>,
        dapp_transaction_results: Arc<RwLock<Vec<DappTransactionResult>>>,
    }

    impl UICallbackState {
        pub fn new() -> Self {
            Self {
                sent_token_transfers: Arc::new(Default::default()),
                token_transfer_results: Arc::new(Default::default()),
                dapp_allotment_transfer_results: Arc::new(Default::default()),
                dapp_transaction_approved: Arc::new(Default::default()),
                dapp_signature_results: Arc::new(Default::default()),
                dapp_transaction_results: Arc::new(Default::default()),
            }
        }

        fn count(&self) -> usize {
            self.sent_token_transfers.read().unwrap().len()
                + self.token_transfer_results.read().unwrap().len()
                + self.dapp_allotment_transfer_results.read().unwrap().len()
                + self.dapp_signature_results.read().unwrap().len()
                + self.dapp_transaction_approved.read().unwrap().len()
                + self.dapp_transaction_results.read().unwrap().len()
        }

        fn add_token_transfer_sent(&self, result: TokenTransferResult) {
            {
                let mut results = self.sent_token_transfers.write().expect("no poison");
                results.push(result)
            }
        }

        fn add_token_transfer_result(&self, result: TokenTransferResult) {
            {
                let mut results = self.token_transfer_results.write().expect("no poison");
                results.push(result)
            }
        }

        fn add_dapp_allotment_transfer_result(
            &self,
            result: DappAllotmentTransferResult,
        ) {
            {
                let mut results = self
                    .dapp_allotment_transfer_results
                    .write()
                    .expect("no poison");
                results.push(result)
            }
        }

        fn add_dapp_signature_result(&self, result: DappSignatureResult) {
            {
                let mut results = self.dapp_signature_results.write().expect("no poison");
                results.push(result)
            }
        }

        fn add_dapp_transaction_approved(&self, result: DappTransactionApproved) {
            {
                let mut results =
                    self.dapp_transaction_approved.write().expect("no poison");
                results.push(result)
            }
        }

        fn add_dapp_transaction_result(&self, result: DappTransactionResult) {
            {
                let mut results =
                    self.dapp_transaction_results.write().expect("no poison");
                results.push(result)
            }
        }
    }

    #[derive(Debug, Clone)]
    pub struct CoreUICallbackMock {
        state: Arc<UICallbackState>,
    }

    impl CoreUICallbackMock {
        pub fn new(state: Arc<UICallbackState>) -> Self {
            Self { state }
        }
    }

    impl CoreUICallbackI for CoreUICallbackMock {
        fn sent_token_transfer(&self, result: TokenTransferResult) {
            self.state.add_token_transfer_sent(result)
        }

        fn token_transfer_result(&self, result: TokenTransferResult) {
            self.state.add_token_transfer_result(result)
        }

        fn dapp_allotment_transfer_result(&self, result: DappAllotmentTransferResult) {
            self.state.add_dapp_allotment_transfer_result(result)
        }

        fn signed_message_for_dapp(&self, result: DappSignatureResult) {
            self.state.add_dapp_signature_result(result)
        }

        fn approved_dapp_transaction(&self, result: DappTransactionApproved) {
            self.state.add_dapp_transaction_approved(result)
        }

        fn dapp_transaction_result(&self, result: DappTransactionResult) {
            self.state.add_dapp_transaction_result(result)
        }
    }

    #[derive(Debug)]
    pub struct InPageCallbackStateMock {
        core: Arc<AppCore>,
        dapp_approval: Arc<RwLock<Option<DappApprovalParams>>>,
        responses: Arc<RwLock<Vec<String>>>,
        notifications: Arc<RwLock<Vec<String>>>,
        page_url: Url,
    }

    impl InPageCallbackStateMock {
        pub fn new(core: Arc<AppCore>, page_url: Url) -> Self {
            Self {
                core,
                dapp_approval: Arc::new(Default::default()),
                responses: Arc::new(Default::default()),
                notifications: Arc::new(Default::default()),
                page_url,
            }
        }

        fn decode_hex(hex_str: &str) -> String {
            let res = hex::decode(hex_str).expect("valid hex");
            String::from_utf8_lossy(&res).into()
        }

        fn update_dapp_approval(&self, dapp_approval: DappApprovalParams) {
            {
                let _ = self
                    .dapp_approval
                    .write()
                    .expect("no poison")
                    .insert(dapp_approval);
            }
        }

        fn add_response(&self, response_hex: String) {
            {
                let mut responses = self.responses.write().expect("no poison");
                responses.push(Self::decode_hex(&response_hex))
            }
        }

        fn add_notification(&self, event_hex: String) {
            {
                let mut notifications = self.notifications.write().expect("no poison");
                notifications.push(Self::decode_hex(&event_hex))
            }
        }
    }

    #[derive(Debug, Clone, TypedBuilder)]
    pub struct InPageRequestContextMockArgs {
        #[builder(default = true)]
        pub user_approves: bool,
        #[builder(default = true)]
        pub transfer_allotment: bool,
    }

    impl Default for InPageRequestContextMockArgs {
        fn default() -> Self {
            InPageRequestContextMockArgs::builder().build()
        }
    }

    // Implement for all targets, not only testing to let the dev server use it too.
    #[derive(Debug)]
    pub struct InPageRequestContextMock {
        pub page_url: String,
        pub callbacks: Box<CoreInPageCallbackMock>,
    }

    impl InPageRequestContextMock {
        pub fn new(
            args: InPageRequestContextMockArgs,
            state: Arc<InPageCallbackStateMock>,
        ) -> Self {
            Self {
                page_url: "https://example.com".into(),
                callbacks: Box::new(CoreInPageCallbackMock::new(args, state)),
            }
        }
    }

    impl InPageRequestContextI for InPageRequestContextMock {
        fn page_url(&self) -> String {
            self.page_url.clone()
        }

        fn callbacks(&self) -> Box<dyn CoreInPageCallbackI> {
            self.callbacks.clone()
        }
    }

    #[derive(Debug, Clone)]
    pub struct CoreInPageCallbackMock {
        args: InPageRequestContextMockArgs,
        state: Arc<InPageCallbackStateMock>,
    }

    impl CoreInPageCallbackMock {
        pub fn new(
            args: InPageRequestContextMockArgs,
            state: Arc<InPageCallbackStateMock>,
        ) -> Self {
            Self { state, args }
        }
    }

    impl CoreInPageCallbackI for CoreInPageCallbackMock {
        fn request_dapp_approval(&self, mut dapp_approval: DappApprovalParams) {
            self.state.update_dapp_approval(dapp_approval.clone());
            let context = Box::new(InPageRequestContextMock::new(
                self.args.clone(),
                self.state.clone(),
            ));
            dapp_approval.transfer_allotment = self.args.transfer_allotment;
            if self.args.user_approves {
                self.state
                    .core
                    .user_approved_dapp(context, dapp_approval)
                    .expect("user_approved_dapp ok")
            } else {
                self.state
                    .core
                    .user_rejected_dapp(context, dapp_approval)
                    .expect("user_rejected_dapp ok")
            }
        }

        fn respond(&self, response_hex: String) {
            self.state.add_response(response_hex)
        }

        fn notify(&self, event_hex: String) {
            self.state.add_notification(event_hex)
        }
    }

    #[test]
    fn no_panic_on_invalid_in_page_request() -> Result<()> {
        let tmp = TmpCore::new()?;
        let context = Box::new(InPageRequestContextMock::new(
            Default::default(),
            tmp.in_page_callback_state.clone(),
        ));

        tmp.core
            .in_page_request(context, "invalid-jsonrpc-payload".to_string())?;

        Ok(())
    }

    #[test]
    fn create_profile() -> Result<()> {
        let tmp = TmpCore::new()?;

        let first_profile = tmp.first_profile();
        let initial_count = tmp.core.list_profiles()?.len();

        let name = "foo".to_string();
        tmp.core.create_profile(name.clone(), "seal-1".into())?;
        let profiles = tmp.core.list_profiles()?;
        assert_eq!(profiles.len(), initial_count + 1);
        assert_eq!(profiles[initial_count].name, name);

        let name = "bar".to_string();
        tmp.core.create_profile(name.clone(), "seal-2".into())?;
        let profiles = tmp.core.list_profiles()?;
        assert_eq!(profiles.len(), initial_count + 2);
        assert_eq!(profiles[initial_count + 1].name, name);

        let last_profile = profiles.last().unwrap();

        let active_profile_id = tmp.core.active_profile_id()?;
        assert_eq!(&active_profile_id, &first_profile.id);

        tmp.core.set_active_profile_id(last_profile.id.clone())?;
        let active_profile_id = tmp.core.active_profile_id()?;
        assert_eq!(&active_profile_id, &last_profile.id);

        Ok(())
    }

    #[test]
    fn active_profile_id() -> Result<()> {
        let tmp = TmpCore::new()?;
        let first_profile = tmp.first_profile();
        let active_profile_id = tmp.core.active_profile_id()?;
        assert_eq!(active_profile_id, first_profile.id);
        Ok(())
    }

    #[test]
    fn profile_has_a_wallet() -> Result<()> {
        let tmp = TmpCore::new()?;
        let first_profile = tmp.first_profile();
        assert_eq!(first_profile.wallets.len(), 1);
        Ok(())
    }

    #[test]
    fn checks_profile_profile_pic_name() -> Result<()> {
        let tmp = TmpCore::new()?;

        let invalid_pic_name = "bar".to_string();
        let result = tmp
            .core
            .create_profile("foo".into(), invalid_pic_name.clone());
        assert!(
            matches!(result, Err(CoreError::Fatal {error }) if error.to_lowercase().contains("not found"))
        );

        Ok(())
    }

    fn setup_profiles(core: &AppCore) -> Result<(String, String)> {
        let keychain = core.resources.keychain();

        core.create_profile("profile-two".into(), "seal-1".into())?;
        let profiles = core.list_profiles()?;
        assert_eq!(profiles.len(), 2);

        let profile_id_one = &profiles[0].id;
        let profile_id_two = &profiles[1].id;

        let res = core.connection_pool().deferred_transaction(|mut tx_conn| {
            let params_one = m::CreateEthAddressParams::builder()
                .profile_id(profile_id_one)
                .chain_id(eth::ChainId::EthMainnet)
                .is_profile_wallet(true)
                .build();
            let from_id = m::Address::create_eth_key_and_address(
                &mut tx_conn,
                keychain,
                &params_one,
            )?;
            let params_two = m::CreateEthAddressParams::builder()
                .profile_id(profile_id_two)
                .chain_id(eth::ChainId::EthMainnet)
                .is_profile_wallet(true)
                .build();
            let to_id = m::Address::create_eth_key_and_address(
                &mut tx_conn,
                keychain,
                &params_two,
            )?;
            let to_address_data =
                m::Address::fetch_eth_signing_key(&mut tx_conn, keychain, &to_id)?;
            let to_address = to_address_data.checksum_address();

            Ok((from_id, to_address))
        })?;
        Ok(res)
    }

    #[test]
    fn cannot_transfer_native_token_between_profiles() -> Result<()> {
        let tmp = TmpCore::new()?;

        let (from_id, to_address) = setup_profiles(&tmp.core)?;
        let args = EthTransferNativeTokenArgs::builder()
            .from_address_id(from_id)
            .to_checksum_address(to_address)
            .amount_decimal("1".into())
            .build();

        let result = tmp.core.eth_transfer_native_token(args);

        assert!(matches!(result, Err(CoreError::User {
                explanation
            }) if explanation.to_lowercase().contains("privacy")));

        Ok(())
    }

    #[test]
    fn cannot_transfer_fungible_token_between_profiles() -> Result<()> {
        let tmp = TmpCore::new()?;

        let (from_id, to_address) = setup_profiles(&tmp.core)?;

        let contract_address: String =
            "0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174".into();
        let args = EthTransferFungibleTokenArgs::builder()
            .from_address_id(from_id)
            .to_checksum_address(to_address)
            .amount_decimal("1.".into())
            .token_id(contract_address)
            .build();
        let result = tmp.core.eth_transfer_fungible_token(args);

        assert!(matches!(result, Err(CoreError::User {
                explanation
            }) if explanation.to_lowercase().contains("privacy")));

        Ok(())
    }

    #[test]
    fn lists_supported_eth_chains() -> Result<()> {
        let tmp = TmpCore::new()?;

        let supported_chains = tmp.core.list_eth_chains();

        assert_eq!(supported_chains.len(), eth::ChainId::iter().len());

        Ok(())
    }

    #[test]
    fn adds_ethereum_chain() -> Result<()> {
        let tmp = TmpCore::new()?;
        let profile_pre = tmp.first_profile();
        let wallets_pre = profile_pre.wallets;
        let wallet = wallets_pre.first().expect("there is a wallet address");

        tmp.core
            .add_eth_chain(eth::ChainId::EthGoerli.into(), wallet.id.clone())?;
        // Check that it's idempotent
        tmp.core
            .add_eth_chain(eth::ChainId::EthGoerli.into(), wallet.id.clone())?;

        let profile_post = tmp.first_profile();
        let wallets_post = profile_post.wallets;
        assert_eq!(wallets_pre.len() + 1, wallets_post.len());

        Ok(())
    }

    fn transfer_native_token_args(tmp: &TmpCore) -> EthTransferNativeTokenArgs {
        let wallet_address = tmp.first_profile_wallet();
        let to_address = ethers::types::Address::random();
        let to_checksum_address = ethers::utils::to_checksum(&to_address, None);
        EthTransferNativeTokenArgs::builder()
            .from_address_id(wallet_address.id)
            .to_checksum_address(to_checksum_address)
            .amount_decimal("1".into())
            .build()
    }

    #[test]
    fn eth_transfer_native_token_success_callbacks() -> Result<()> {
        let tmp = TmpCore::new()?;

        let chain_id = eth::ChainId::default_wallet_chain();
        tmp.fund_first_profile_wallet(chain_id);

        let args = transfer_native_token_args(&tmp);
        tmp.core.eth_transfer_native_token(args)?;

        tmp.wait_for_ui_callbacks(2);
        let sent_results = tmp.sent_token_transfers();
        assert_eq!(sent_results.len(), 1);
        assert!(sent_results[0].error_message.is_none());
        let transfer_results = tmp.token_transfer_results();
        assert!(transfer_results[0].error_message.is_none());
        assert!(transfer_results[0].explorer_url.is_some());

        Ok(())
    }

    #[test]
    fn eth_transfer_native_token_error_callbacks() -> Result<()> {
        let tmp = TmpCore::new()?;

        let args = transfer_native_token_args(&tmp);
        tmp.core.eth_transfer_native_token(args)?;

        // This only tests if the tx is outright rejected.
        tmp.wait_for_ui_callbacks(1);
        let sent_results = tmp.token_transfer_results();
        assert_eq!(sent_results.len(), 1);
        assert!(sent_results[0].error_message.is_some());
        let error_message = sent_results[0].error_message.as_ref().unwrap();
        assert!(error_message.to_lowercase().contains("funds"));

        Ok(())
    }

    #[test]
    fn native_token_for_address() -> Result<()> {
        let tmp = TmpCore::new()?;
        let profile = tmp.first_profile();
        let address_id = profile.wallets.first().map(|a| &a.id).unwrap();

        let token = tmp.core.native_token_for_address(address_id.clone())?;
        assert_eq!(token.amount, Some("0".into()));

        Ok(())
    }

    #[test]
    fn runs_data_migrations() -> Result<()> {
        let tmp = TmpCore::new()?;
        let version = tmp.data_migration_version()?;
        assert!(version.is_some());
        Ok(())
    }

    #[test]
    fn top_dapps() -> Result<()> {
        let tmp = TmpCore::new()?;
        let top_dapps = tmp.core.top_dapps(10)?;
        assert!(!top_dapps.is_empty());
        Ok(())
    }

    #[test]
    fn enable_backup_error_if_cant_backup() -> Result<()> {
        let tmp = TmpCore::with_overrides(true)?;

        let res = tmp.core.enable_backup();
        assert!(matches!(res, Err(BackupError::BackupDisabled)));
        assert!(!tmp.core.is_backup_enabled()?);

        Ok(())
    }

    #[test]
    fn can_enable_backup() -> Result<()> {
        let tmp = TmpCore::new()?;

        tmp.core.enable_backup()?;
        assert!(tmp.core.is_backup_enabled()?);

        Ok(())
    }
}
