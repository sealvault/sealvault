// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use typed_builder::TypedBuilder;

use crate::{
    backup::BackupStorageI,
    db::ConnectionPool,
    device::{DeviceIdentifier, DeviceName},
    encryption::Keychain,
    http_client::HttpClient,
    protocols::eth,
    public_suffix_list::PublicSuffixList,
    CoreUICallbackI,
};

/// Let us inject mock resources and retain references to them without type erasure.
pub trait CoreResourcesI: Debug + Send + Sync {
    fn ui_callbacks(&self) -> &dyn CoreUICallbackI;
    fn connection_pool(&self) -> &ConnectionPool;
    fn keychain(&self) -> &Keychain;
    fn http_client(&self) -> &HttpClient;
    fn rpc_manager(&self) -> &dyn eth::RpcManagerI;
    fn public_suffix_list(&self) -> &PublicSuffixList;
    fn backup_storage(&self) -> &dyn BackupStorageI;
    fn device_id(&self) -> &DeviceIdentifier;
    fn device_name(&self) -> &DeviceName;
}

// All Send + Sync. Grouped in this struct to simplify getting an Arc to all.
#[derive(Debug, TypedBuilder)]
#[readonly::make]
pub struct CoreResources {
    ui_callbacks: Box<dyn CoreUICallbackI>,
    connection_pool: ConnectionPool,
    keychain: Keychain,
    http_client: HttpClient,
    rpc_manager: Box<dyn eth::RpcManagerI>,
    public_suffix_list: PublicSuffixList,
    backup_storage: Box<dyn BackupStorageI>,
    device_name: DeviceName,
    device_id: DeviceIdentifier,
}

impl CoreResourcesI for CoreResources {
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
