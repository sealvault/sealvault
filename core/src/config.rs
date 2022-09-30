// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::time::Duration;

// Thread pools
// We're just one app among many on the user's device, keep the footprint low.
pub const DB_CONNECTION_POOL_SIZE: u32 = 4;
pub const TOKIO_WORKER_THREADS: usize = 1;
pub const TOKIO_MAX_BLOCKING_THREADS: usize = 8;

// User
pub const DEFAULT_ACCOUNT_NAME: &str = "Default";
pub const DEFAULT_ACCOUNT_PICTURE_NAME: &str = "cat-green";

// Cryptography
pub const SK_DEK_NAME: &str = "SK-DATA-ENCRYPTION-KEY";
pub const SK_KEK_NAME: &str = "SK-KEY-ENCRYPTION-KEY";

// In-page provider
pub const MAX_JSONRPC_REQUEST_SIZE_BYTES: usize = 1000000;
pub const MAX_JSONRPC_RESPONSE_SIZE_BYTES: usize = 1000000;

// Assets
pub const IN_PAGE_PROVIDER_FILE_NAME: &str = "in-page-provider.js";
pub const JS_PREFIX: &str = "js";
pub const PROFILE_PIC_PREFIX: &str = "profile-pics";
pub const PROFILE_PIC_EXTENSION: &str = ".jpeg";
pub const RPC_PROVIDER_PLACEHOLDER: &str = "<SEALVAULT_RPC_PROVIDER>";
pub const REQUEST_HANDLER_PLACEHOLDER: &str = "<SEALVAULT_REQUEST_HANDLER>";
pub const DEFAULT_CHAIN_ID_PLACEHOLDER: &str = "<SEALVAULT_DEFAULT_CHAIN_ID>";
pub const DEFAULT_NETWORK_VERSION_PLACEHOLDER: &str = "<SEALVAULT_DEFAULT_NETWORK_VERSION>";
pub const ETH_NATIVE_TOKEN_PREFIX: &str = "protocols/eth/native-tokens";
pub const NATIVE_TOKEN_EXTENSION: &str = ".png";
pub const FALLBACK_FAVICON_ASSET: &str = "fallback-favicon.png";

// Public Suffix List
pub const PUBLIC_SUFFIX_LIST_ASSET: &str = "public-suffix-list.dat.txt";
// Latest version
pub const PUBLIC_SUFFIX_LIST_URL: &str =
    "https://publicsuffix.org/list/public_suffix_list.dat";
// 1 day recommended by https://publicsuffix.org/list/
pub const PUBLIC_SUFFIX_POLL: Duration = Duration::from_secs(24 * 60 * 60);

// Favicons
pub const FAVICON_API: &str = "https://icons.duckduckgo.com/ip3/";

// iOS
pub const IOS_SERVICE: &str = "org.sealvault";
