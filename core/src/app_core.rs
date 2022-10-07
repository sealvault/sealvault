// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::db::models as m;
use crate::db::schema_migrations::run_migrations;
use crate::db::{data_migrations, ConnectionPool};
use crate::encryption::Keychain;
use crate::error::Error;
use crate::http_client::HttpClient;
use crate::in_page_provider::{InPageProvider, InPageRequestContextI};
use crate::protocols::eth;
use crate::public_suffix_list::PublicSuffixList;
use crate::{dto, in_page_provider, CoreError};
use std::fmt::Debug;
use std::sync::Arc;

/// Provides cross-platform key and transaction management.
/// Exposed to host language via FFI.
/// The methods take ownership of arguments, because FFI needs owning interfaces.
/// All members are `Send + Sync + 'static`.
/// No async interfaces, because concurrency is managed by the host languages.
pub struct AppCore {
    resources: Arc<CoreResources>,
}

// All Send + Sync. Grouped in this struct to simplify getting an Arc to all.
#[derive(Debug)]
#[readonly::make]
pub struct CoreResources {
    pub connection_pool: ConnectionPool,
    pub keychain: Keychain,
    pub http_client: HttpClient,
    pub rpc_manager: Box<dyn eth::RpcManagerI>,
    pub public_suffix_list: PublicSuffixList,
}

impl AppCore {
    pub fn new(args: CoreArgs) -> Result<Self, CoreError> {
        let rpc_manager = Box::new(eth::RpcManager::new());
        Self::new_with_overrides(args, rpc_manager)
    }

    fn connection_pool(&self) -> &ConnectionPool {
        &self.resources.connection_pool
    }

    fn keychain(&self) -> &Keychain {
        &self.resources.keychain
    }

    fn rpc_manager(&self) -> &dyn eth::RpcManagerI {
        &*self.resources.rpc_manager
    }

    fn assembler(&self) -> dto::Assembler {
        dto::Assembler::new(self.resources.clone())
    }

    /// Let us mock functionality. Not exposed through FFI.
    pub fn new_with_overrides(
        args: CoreArgs,
        rpc_manager: Box<dyn eth::RpcManagerI>,
    ) -> Result<Self, CoreError> {
        let connection_pool = ConnectionPool::new(&args.db_file_path)?;

        let keychain = Keychain::new();

        // Run DB schema migrations and data migrations that haven't been applied yet.
        connection_pool.exclusive_transaction(|mut tx_conn| {
            run_migrations(&mut tx_conn)?;
            data_migrations::run_all(tx_conn, &keychain)
        })?;

        let public_suffix_list = PublicSuffixList::new()?;

        let http_client = HttpClient::new(args.cache_dir);
        let resources = CoreResources {
            rpc_manager,
            connection_pool,
            keychain,
            http_client,
            public_suffix_list,
        };

        Ok(AppCore {
            resources: Arc::new(resources),
        })
    }

    pub fn list_accounts(&self) -> Result<Vec<dto::CoreAccount>, CoreError> {
        let res = self.assembler().assemble_accounts()?;
        Ok(res)
    }

    pub fn active_account_id(&self) -> Result<String, CoreError> {
        let mut conn = self.connection_pool().connection()?;
        let res = m::LocalSettings::fetch_active_account_id(&mut conn)?;
        Ok(res)
    }

    pub fn create_account(
        &self,
        name: String,
        bundled_picture_name: String,
    ) -> Result<Vec<dto::CoreAccount>, CoreError> {
        self.connection_pool().deferred_transaction(|mut tx_conn| {
            let account_params = m::AccountParams::builder()
                .name(&*name)
                .bundled_picture_name(&*bundled_picture_name)
                .build();
            m::Account::create_eth_account(
                &mut tx_conn,
                self.keychain(),
                &account_params,
            )?;
            Ok(())
        })?;

        self.list_accounts()
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
        let _ = provider.in_page_request(raw_request);
        Ok(())
    }

    fn fetch_eth_signing_key_for_transfer(
        &self,
        from_address_id: &str,
        to_checksum_address: &str,
    ) -> Result<eth::SigningKey, Error> {
        let signing_key = self.connection_pool().deferred_transaction(|mut tx_conn| {
            // Returns NotFoundError if the address is not in the db.
            let from_account_id =
                m::Address::fetch_account_id(tx_conn.as_mut(), from_address_id)?;
            let maybe_to_account_id = m::Address::fetch_account_id_for_eth_address(
                tx_conn.as_mut(),
                to_checksum_address,
            )?;

            // See privacy in developer docs fore more.
            if maybe_to_account_id.is_some()
                && Some(from_account_id) != maybe_to_account_id
            {
                return Err(Error::User {
                    explanation: "Cannot transfer between accounts for privacy reasons."
                        .into(),
                })?;
            }

            m::Address::fetch_eth_signing_key(
                &mut tx_conn,
                self.keychain(),
                from_address_id,
            )
        })?;
        Ok(signing_key)
    }

    /// Transfer native token on an Ethereum protocol network.
    /// Returns the tx hash that can be used to poll for the result.
    pub fn eth_transfer_native_token(
        &self,
        from_address_id: String,
        to_checksum_address: String,
        amount_decimal: String,
    ) -> Result<String, CoreError> {
        let signing_key = self
            .fetch_eth_signing_key_for_transfer(&from_address_id, &to_checksum_address)?;

        let amount = eth::NativeTokenAmount::new_from_decimal(
            signing_key.chain_id,
            &amount_decimal,
        )?;
        let rpc_provider = self.rpc_manager().eth_api_provider(signing_key.chain_id);
        let tx_hash = rpc_provider.transfer_native_token(
            &signing_key,
            &to_checksum_address,
            &amount,
        )?;

        Ok(tx_hash)
    }

    /// Transfer fungible native token on an Ethereum protocol network.
    /// Returns the tx hash that can be used to poll for the result.
    pub fn eth_transfer_fungible_token(
        &self,
        from_address_id: String,
        to_checksum_address: String,
        amount_decimal: String,
        token_id: String,
    ) -> Result<String, CoreError> {
        // TODO we use contract address as token id for now, but it should be chain specific
        let contract_address = &token_id;
        let signing_key = self
            .fetch_eth_signing_key_for_transfer(&from_address_id, &to_checksum_address)?;

        let rpc_provider = self.rpc_manager().eth_api_provider(signing_key.chain_id);
        let tx_hash = rpc_provider.transfer_fungible_token(
            &signing_key,
            &to_checksum_address,
            &amount_decimal,
            contract_address,
        )?;

        Ok(tx_hash)
    }

    /// Get the block explorer link for a transaction
    pub fn eth_transaction_block_explorer_url(
        &self,
        from_address_id: String,
        tx_hash: String,
    ) -> Result<String, CoreError> {
        let mut conn = self.connection_pool().connection()?;
        let chain_id = m::Address::fetch_eth_chain_id(&mut conn, &from_address_id)?;
        let url = eth::explorer::tx_url(chain_id, &tx_hash)?;
        Ok(url.to_string())
    }
}

#[derive(Debug, Clone)]
pub struct CoreArgs {
    pub cache_dir: String,
    pub db_file_path: String,
}

#[cfg(test)]
pub mod tests {

    use super::*;
    use crate::protocols::ChecksumAddress;
    use crate::{CoreInPageCallbackI, DappApprovalParams};
    use anyhow::Result;
    use std::fs;
    use std::sync::RwLock;
    use tempfile::TempDir;

    #[readonly::make]
    pub(crate) struct TmpCoreDir {
        // The TempDir is kept to keep it open for the lifetime of the backend as the db file is
        // deleted when in the TempDir dtor is invoked.
        #[allow(dead_code)]
        pub tmp_dir: TempDir,
        pub cache_dir: String,
        pub db_file_path: String
    }

    impl TmpCoreDir {
        pub fn new() -> Result<Self, Error> {
            // Important not to use in-memory DB as Sqlite has subtle differences in in memory
            // mode.
            let tmp_dir = tempfile::tempdir().map_err(|err| Error::Fatal {
                error: err.to_string(),
            })?;
            let db_dir = tmp_dir.path().join("db");
            let cache_dir = tmp_dir.path().join("cache");

            fs::create_dir(&db_dir).unwrap();
            fs::create_dir(&cache_dir).unwrap();

            let db_file_path = db_dir
                .join("tmp-db.sqlite3")
                .into_os_string()
                .into_string()
                .unwrap();

            let cache_dir = cache_dir.into_os_string().into_string().map_err(|err| Error::Fatal {
                error: format!("{:?}", err)
            })?;

            Ok(Self {
                tmp_dir,
                cache_dir,
                db_file_path
            })
        }
    }

    /// Create an empty path in a temp directory for a Sqlite DB.
    pub(crate) struct TmpCore {
        pub core: AppCore,
        #[allow(dead_code)]
        tmp_dir: TmpCoreDir,
        in_page_callback_state: Arc<InPageCallbackState>,
    }

    impl TmpCore {
        pub fn new() -> Result<Self, CoreError> {
            // Important not to use in-memory DB as Sqlite has subtle differences in in memory
            // mode.
            let tmp_dir = TmpCoreDir::new()?;

            let rpc_manager = Box::new(eth::AnvilRpcManager::new());

            let backend_args = CoreArgs {
                cache_dir: tmp_dir.cache_dir.clone(),
                db_file_path: tmp_dir.db_file_path.clone(),
            };
            let backend = AppCore::new_with_overrides(backend_args, rpc_manager)?;
            Ok(TmpCore {
                core: backend,
                tmp_dir,
                in_page_callback_state: Arc::new(Default::default()),
            })
        }

        pub fn data_migration_version(&self) -> Result<Option<String>, Error> {
            let mut conn = self.core.connection_pool().connection()?;
            let mut migrations = m::DataMigration::list_all(&mut conn)?;
            migrations.sort_by_key(|m| m.version.clone());
            Ok(migrations.last().map(|m| m.version.clone()))
        }

        pub fn first_account(&self) -> dto::CoreAccount {
            let accounts = self.core.list_accounts().expect("cannot list accounts");
            accounts.into_iter().next().expect("no accounts")
        }

        pub fn in_page_provider(
            &self,
            page_url: &str,
            user_approves: bool,
        ) -> InPageProvider {
            let context = Box::new(InPageRequestContextMock::new(
                page_url,
                user_approves,
                self.in_page_callback_state.clone(),
            ));

            InPageProvider::new(self.core.resources.clone(), context).expect("url valid")
        }

        pub fn dapp_approval(&self) -> Option<DappApprovalParams> {
            self.in_page_callback_state
                .dapp_approval
                .read()
                .unwrap()
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
    }

    #[derive(Debug, Default)]
    pub struct InPageCallbackState {
        dapp_approval: Arc<RwLock<Option<DappApprovalParams>>>,
        responses: Arc<RwLock<Vec<String>>>,
        notifications: Arc<RwLock<Vec<String>>>,
    }

    impl InPageCallbackState {
        pub fn new() -> Self {
            Self {
                dapp_approval: Arc::new(Default::default()),
                responses: Arc::new(Default::default()),
                notifications: Arc::new(Default::default()),
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

    // Implement for all targets, not only testing to let the dev server use it too.
    #[derive(Debug)]
    pub struct InPageRequestContextMock {
        pub page_url: String,
        pub callbacks: Box<CoreInPageCallbackMock>,
    }

    impl InPageRequestContextMock {
        pub fn new(
            page_url: &str,
            user_approves: bool,
            state: Arc<InPageCallbackState>,
        ) -> Self {
            Self {
                page_url: page_url.into(),
                callbacks: Box::new(CoreInPageCallbackMock::new(user_approves, state)),
            }
        }
        pub fn default_boxed(state: Arc<InPageCallbackState>) -> Box<Self> {
            Box::new(InPageRequestContextMock::new(
                "https://example.com",
                true,
                state,
            ))
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
        user_approves: bool,
        state: Arc<InPageCallbackState>,
    }

    impl CoreInPageCallbackMock {
        pub fn new(user_approves: bool, state: Arc<InPageCallbackState>) -> Self {
            Self {
                state,
                user_approves,
            }
        }
    }

    impl CoreInPageCallbackI for CoreInPageCallbackMock {
        fn approve_dapp(&self, dapp_approval: DappApprovalParams) -> bool {
            self.state.update_dapp_approval(dapp_approval);
            self.user_approves
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
        let state: Arc<InPageCallbackState> = Arc::new(Default::default());
        let context = Box::new(InPageRequestContextMock::new(
            "https://example.com",
            true,
            state.clone(),
        ));

        tmp.core
            .in_page_request(context, "invalid-jsonrpc-payload".to_string())?;

        Ok(())
    }

    #[test]
    fn create_account() -> Result<()> {
        let tmp = TmpCore::new()?;

        let initial_count = tmp.core.list_accounts()?.len();

        let name = "foo".to_string();
        let accounts = tmp.core.create_account(name.clone(), "pug-yellow".into())?;
        assert_eq!(accounts.len(), initial_count + 1);
        assert_eq!(accounts[initial_count].name, name);

        let name = "bar".to_string();
        let accounts = tmp.core.create_account(name.clone(), "pug-denim".into())?;
        assert_eq!(accounts.len(), initial_count + 2);
        assert_eq!(accounts[initial_count + 1].name, name);

        Ok(())
    }

    #[test]
    fn active_account_id() -> Result<()> {
        let tmp = TmpCore::new()?;
        let first_account = tmp.first_account();
        let active_account_id = tmp.core.active_account_id()?;
        assert_eq!(active_account_id, first_account.id);
        Ok(())
    }

    #[test]
    fn checks_account_profile_pic_name() -> Result<()> {
        let tmp = TmpCore::new()?;

        let invalid_pic_name = "bar".to_string();
        let result = tmp
            .core
            .create_account("foo".into(), invalid_pic_name.clone());
        assert!(
            matches!(result, Err(CoreError::Fatal {error }) if error.to_lowercase().contains("not found"))
        );

        Ok(())
    }

    fn setup_accounts(core: &AppCore) -> Result<(String, String)> {
        let keychain = &core.resources.keychain;

        let accounts = core.create_account("account-two".into(), "pug-yellow".into())?;
        assert_eq!(accounts.len(), 2);

        let account_id_one = &accounts[0].id;
        let account_id_two = &accounts[1].id;

        let res = core.connection_pool().deferred_transaction(|mut tx_conn| {
            let from_id = m::Address::create_eth_key_and_address(
                &mut tx_conn,
                keychain,
                account_id_one,
                eth::ChainId::EthMainnet,
                None,
                true,
            )?;
            let to_id = m::Address::create_eth_key_and_address(
                &mut tx_conn,
                keychain,
                account_id_two,
                eth::ChainId::EthMainnet,
                None,
                true,
            )?;
            let to_address_data =
                m::Address::fetch_eth_signing_key(&mut tx_conn, keychain, &to_id)?;
            let to_address = to_address_data.checksum_address();

            Ok((from_id, to_address))
        })?;
        Ok(res)
    }

    #[test]
    fn cannot_transfer_native_token_between_accounts() -> Result<()> {
        let tmp = TmpCore::new()?;

        let (from_id, to_address) = setup_accounts(&tmp.core)?;

        let result = tmp
            .core
            .eth_transfer_native_token(from_id, to_address, "1".into());

        assert!(matches!(result, Err(CoreError::User {
                explanation
            }) if explanation.to_lowercase().contains("privacy")));

        Ok(())
    }

    #[test]
    fn cannot_transfer_fungible_token_between_accounts() -> Result<()> {
        let tmp = TmpCore::new()?;

        let (from_id, to_address) = setup_accounts(&tmp.core)?;

        let contract_address: String =
            "0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174".into();
        let result = tmp.core.eth_transfer_fungible_token(
            from_id,
            to_address,
            "1".into(),
            contract_address,
        );

        assert!(matches!(result, Err(CoreError::User {
                explanation
            }) if explanation.to_lowercase().contains("privacy")));

        Ok(())
    }

    #[test]
    fn native_token_for_address() -> Result<()> {
        let tmp = TmpCore::new()?;
        let account = tmp.first_account();
        let address_id = account.wallets.first().map(|a| &a.id).unwrap();

        let token = tmp.core.native_token_for_address(address_id.clone())?;
        assert_eq!(token.amount, Some("0".into()));

        Ok(())
    }

    #[test]
    fn runs_data_migration_v0() -> Result<()> {
        let tmp = TmpCore::new()?;
        let version = tmp.data_migration_version()?;
        assert_eq!(version.expect("there is data migration"), "v0");
        Ok(())
    }
}
