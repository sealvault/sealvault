// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{fmt::Debug, sync::Arc};

use crate::{
    db::{
        data_migrations, models as m, schema_migrations::run_migrations, ConnectionPool,
    },
    dto,
    encryption::Keychain,
    error::Error,
    http_client::HttpClient,
    in_page_provider,
    in_page_provider::{InPageProvider, InPageRequestContextI},
    protocols::eth,
    public_suffix_list::PublicSuffixList,
    CoreError, CoreUICallbackI, DappApprovalParams,
};

/// Provides cross-platform key and transaction management.
/// Exposed to host language via FFI.
/// The methods take ownership of arguments, because FFI needs owning interfaces.
/// All members are `Send + Sync + 'static`.
/// No async interfaces, because concurrency is managed by the host languages.
#[derive(Debug)]
pub struct AppCore {
    resources: Arc<CoreResources>,
}

// All Send + Sync. Grouped in this struct to simplify getting an Arc to all.
#[derive(Debug)]
#[readonly::make]
pub struct CoreResources {
    pub ui_callbacks: Box<dyn CoreUICallbackI>,
    pub connection_pool: ConnectionPool,
    pub keychain: Keychain,
    pub http_client: HttpClient,
    pub rpc_manager: Box<dyn eth::RpcManagerI>,
    pub public_suffix_list: PublicSuffixList,
}

#[derive(Debug)]
pub struct CoreArgs {
    pub cache_dir: String,
    pub db_file_path: String,
}

impl AppCore {
    // UI callbacks cannot be part of the args struct, because Uniffi expects it to be hashable
    // then.
    pub fn new(
        args: CoreArgs,
        ui_callbacks: Box<dyn CoreUICallbackI>,
    ) -> Result<Self, CoreError> {
        let rpc_manager = Box::new(eth::RpcManager::new());
        Self::new_with_overrides(args, ui_callbacks, rpc_manager)
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
        ui_callbacks: Box<dyn CoreUICallbackI>,
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
            ui_callbacks,
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

    pub fn user_approved_dapp(
        &self,
        context: Box<dyn InPageRequestContextI>,
        dapp_approval: DappApprovalParams,
    ) -> Result<(), CoreError> {
        let resources = self.resources.clone();
        let provider = InPageProvider::new(resources, context)?;
        let _ = provider.user_approved_dapp(dapp_approval);
        Ok(())
    }

    pub fn user_rejected_dapp(
        &self,
        context: Box<dyn InPageRequestContextI>,
        dapp_approval: DappApprovalParams,
    ) -> Result<(), CoreError> {
        let resources = self.resources.clone();
        let provider = InPageProvider::new(resources, context)?;
        let _ = provider.user_rejected_dapp(dapp_approval);
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

    /// List supported Ethereum chains.
    pub fn list_eth_chains(&self) -> Vec<dto::CoreEthChain> {
        self.assembler().list_eth_chains()
    }
}

#[cfg(test)]
pub mod tests {

    use std::{fs, sync::RwLock, thread, time::Duration};

    use anyhow::Result;
    use strum::IntoEnumIterator;
    use tempfile::TempDir;
    use url::Url;

    use super::*;
    use crate::{
        protocols::ChecksumAddress, CoreInPageCallbackI, DappAllotmentTransferResult,
        DappApprovalParams,
    };

    #[readonly::make]
    pub(crate) struct TmpCoreDir {
        // The TempDir is kept to keep it open for the lifetime of the core as the db file is
        // deleted when in the TempDir dtor is invoked.
        #[allow(dead_code)]
        pub tmp_dir: TempDir,
        pub cache_dir: String,
        pub db_file_path: String,
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

            let cache_dir =
                cache_dir
                    .into_os_string()
                    .into_string()
                    .map_err(|err| Error::Fatal {
                        error: format!("{:?}", err),
                    })?;

            Ok(Self {
                tmp_dir,
                cache_dir,
                db_file_path,
            })
        }
    }

    /// Create an empty path in a temp directory for a Sqlite DB.
    pub(crate) struct TmpCore {
        pub core: Arc<AppCore>,
        #[allow(dead_code)]
        tmp_dir: TmpCoreDir,
        ui_callback_state: Arc<UICallbackState>,
        in_page_callback_state: Arc<InPageCallbackState>,
    }

    impl TmpCore {
        pub fn new() -> Result<Self, CoreError> {
            // Important not to use in-memory DB as Sqlite has subtle differences in in memory
            // mode.
            let tmp_dir = TmpCoreDir::new()?;

            let rpc_manager = Box::new(eth::AnvilRpcManager::new());

            let ui_callback_state = Arc::new(UICallbackState::new());
            let ui_callbacks =
                Box::new(CoreUICallbackMock::new(ui_callback_state.clone()));

            let core_args = CoreArgs {
                cache_dir: tmp_dir.cache_dir.clone(),
                db_file_path: tmp_dir.db_file_path.clone(),
            };
            let core = Arc::new(AppCore::new_with_overrides(
                core_args,
                ui_callbacks,
                rpc_manager,
            )?);

            let page_url = Url::parse("https://example.com").expect("static url ok");
            let in_page_callback_state =
                Arc::new(InPageCallbackState::new(core.clone(), page_url));
            Ok(TmpCore {
                core,
                tmp_dir,
                ui_callback_state,
                in_page_callback_state,
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

        pub fn in_page_provider(&self, user_approves: bool) -> InPageProvider {
            let context = Box::new(InPageRequestContextMock::new(
                user_approves,
                self.in_page_callback_state.clone(),
            ));

            InPageProvider::new(self.core.resources.clone(), context).expect("url valid")
        }

        pub fn wait_for_first_in_page_response(&self) {
            const WAIT_FOR_MILLIS: usize = 1000;

            for _ in 0..WAIT_FOR_MILLIS {
                thread::sleep(Duration::from_millis(1));
                // Don't hold the lock while sleeping.
                if !self.responses().is_empty() {
                    break;
                }
            }
        }

        pub fn wait_for_dapp_allotment_transfer(&self) {
            const WAIT_FOR_MILLIS: usize = 1000;

            for _ in 0..WAIT_FOR_MILLIS {
                thread::sleep(Duration::from_millis(1));
                // Don't hold the lock while sleeping.
                if !self.dapp_allotment_transfer_results().is_empty() {
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

        pub fn dapp_allotment_transfer_results(
            &self,
        ) -> Vec<DappAllotmentTransferResult> {
            self.ui_callback_state
                .dapp_allotment_transfer_results
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
        dapp_allotment_transfer_results: Arc<RwLock<Vec<DappAllotmentTransferResult>>>,
    }

    impl UICallbackState {
        pub fn new() -> Self {
            Self {
                dapp_allotment_transfer_results: Arc::new(Default::default()),
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
        fn dapp_allotment_transfer_result(&self, result: DappAllotmentTransferResult) {
            self.state.add_dapp_allotment_transfer_result(result)
        }
    }

    #[derive(Debug)]
    pub struct InPageCallbackState {
        core: Arc<AppCore>,
        dapp_approval: Arc<RwLock<Option<DappApprovalParams>>>,
        responses: Arc<RwLock<Vec<String>>>,
        notifications: Arc<RwLock<Vec<String>>>,
        page_url: Url,
    }

    impl InPageCallbackState {
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

    // Implement for all targets, not only testing to let the dev server use it too.
    #[derive(Debug)]
    pub struct InPageRequestContextMock {
        pub page_url: String,
        pub callbacks: Box<CoreInPageCallbackMock>,
    }

    impl InPageRequestContextMock {
        pub fn new(user_approves: bool, state: Arc<InPageCallbackState>) -> Self {
            Self {
                page_url: "https://example.com".into(),
                callbacks: Box::new(CoreInPageCallbackMock::new(user_approves, state)),
            }
        }
        pub fn default_boxed(state: Arc<InPageCallbackState>) -> Box<Self> {
            Box::new(InPageRequestContextMock::new(true, state))
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
        fn request_dapp_approval(&self, dapp_approval: DappApprovalParams) {
            self.state.update_dapp_approval(dapp_approval.clone());
            let context = Box::new(InPageRequestContextMock::new(
                self.user_approves,
                self.state.clone(),
            ));
            if self.user_approves {
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
            true,
            tmp.in_page_callback_state.clone(),
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
            let params_one = m::CreateEthAddressParams::builder()
                .account_id(account_id_one)
                .chain_id(eth::ChainId::EthMainnet)
                .is_account_wallet(true)
                .build();
            let from_id = m::Address::create_eth_key_and_address(
                &mut tx_conn,
                keychain,
                &params_one,
            )?;
            let params_two = m::CreateEthAddressParams::builder()
                .account_id(account_id_two)
                .chain_id(eth::ChainId::EthMainnet)
                .is_account_wallet(true)
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
    fn lists_supported_eth_chains() -> Result<()> {
        let tmp = TmpCore::new()?;

        let supported_chains = tmp.core.list_eth_chains();

        assert_eq!(supported_chains.len(), eth::ChainId::iter().len());

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
