// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
mod dapp_key_provider;

pub use dapp_key_provider::{
    CoreInPageCallbackI, DappApprovalParams, DappKeyProvider, InPageErrorCode,
    InPageRequestContextI,
};

use crate::{assets, config, protocols::eth, Error};

pub fn load_in_page_provider_script(
    rpc_provider_name: &str,
    request_handler_name: &str,
) -> Result<String, Error> {
    let chain_id = eth::ChainId::default_dapp_chain();
    let network_version = chain_id.network_version();
    let hex_chain_id = chain_id.display_hex();
    let replacements = vec![
        (config::RPC_PROVIDER_PLACEHOLDER, rpc_provider_name),
        (config::REQUEST_HANDLER_PLACEHOLDER, request_handler_name),
        (config::DEFAULT_CHAIN_ID_PLACEHOLDER, &hex_chain_id),
        (
            config::DEFAULT_NETWORK_VERSION_PLACEHOLDER,
            &network_version,
        ),
    ];

    let path = format!(
        "{}/{}",
        config::JS_PREFIX,
        config::IN_PAGE_PROVIDER_FILE_NAME
    );
    let text = assets::load_asset_with_replacements(&path, replacements.iter())?;

    Ok(text)
}
