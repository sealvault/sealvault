// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use uniffi_sealvault_core::{
    CoreBackupStorageI, CoreInPageCallbackI, CoreUICallbackI,
    DappAllotmentTransferResult, DappApprovalParams, DappSignatureResult,
    DappTransactionApproved, DappTransactionResult, InPageRequestContextI,
    TokenTransferResult,
};

#[derive(Debug, Default)]
pub struct CoreUICallBackMock {}

impl CoreUICallBackMock {
    pub fn new() -> Self {
        Self {}
    }
}

impl CoreUICallbackI for CoreUICallBackMock {
    fn sent_token_transfer(&self, result: TokenTransferResult) {
        log::debug!("Sent token transfer: {:?}", result)
    }

    fn token_transfer_result(&self, result: TokenTransferResult) {
        log::debug!("Token transfer result: {:?}", result)
    }

    fn dapp_allotment_transfer_result(&self, result: DappAllotmentTransferResult) {
        log::debug!("Dapp allotment transfer result: {:?}", result)
    }

    fn signed_message_for_dapp(&self, result: DappSignatureResult) {
        log::debug!("Dapp signature result: {:?}", result)
    }

    fn approved_dapp_transaction(&self, result: DappTransactionApproved) {
        log::debug!("Sent transactions for dapp result: {:?}", result)
    }

    fn dapp_transaction_result(&self, result: DappTransactionResult) {
        log::debug!("Dapp transaction result: {:?}", result)
    }
}

#[derive(Debug)]
pub struct InPageRequestContextMock {
    pub page_url: String,
    pub callbacks: Box<CoreInPageCallbackMock>,
}

impl InPageRequestContextMock {
    pub fn new(page_url: &str) -> Self {
        Self {
            page_url: page_url.into(),
            callbacks: Box::new(CoreInPageCallbackMock::new()),
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
pub struct CoreInPageCallbackMock {}

impl CoreInPageCallbackMock {
    // We don't want to create the mock by accident with `Default::default`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {}
    }
}

impl CoreInPageCallbackI for CoreInPageCallbackMock {
    fn request_dapp_approval(&self, params: DappApprovalParams) {
        log::debug!("Request dapp approval: {params:?}")
    }

    fn respond(&self, response_hex: String) {
        let response = hex::decode(response_hex).expect("valid hex");
        let response = String::from_utf8_lossy(&response);
        log::debug!("In-page callback response: '{response}'");
    }

    fn notify(&self, message_hex: String) {
        let event = hex::decode(message_hex).expect("valid hex");
        let event = String::from_utf8_lossy(&event);
        log::debug!("In-page callback notification: '{event}'");
    }
}

#[derive(Debug, Clone)]
pub struct CoreBackupStorageMock {}

impl CoreBackupStorageMock {
    // We don't want to create the mock by accident with `Default::default`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {}
    }
}

impl CoreBackupStorageI for CoreBackupStorageMock {
    fn can_backup(&self) -> bool {
        false
    }

    fn is_uploaded(&self, _: String) -> bool {
        false
    }

    fn list_backup_file_names(&self) -> Vec<String> {
        Default::default()
    }

    fn copy_to_storage(&self, _: String, _: String) -> bool {
        false
    }

    fn copy_from_storage(&self, _: String, _: String) -> bool {
        false
    }

    fn delete_backup(&self, _: String) -> bool {
        false
    }
}
