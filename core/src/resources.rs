use std::fmt::Debug;

use typed_builder::TypedBuilder;

use crate::{
    db::ConnectionPool, encryption::Keychain, http_client::HttpClient, protocols::eth,
    public_suffix_list::PublicSuffixList, CoreUICallbackI,
};

/// Let us inject mock resources and retain references to them without type erasure.
pub trait CoreResourcesI: Debug + Send + Sync {
    fn ui_callbacks(&self) -> &dyn CoreUICallbackI;
    fn connection_pool(&self) -> &ConnectionPool;
    fn keychain(&self) -> &Keychain;
    fn http_client(&self) -> &HttpClient;
    fn rpc_manager(&self) -> &dyn eth::RpcManagerI;
    fn public_suffix_list(&self) -> &PublicSuffixList;
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
}
