// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

#![no_main]

use libfuzzer_sys::fuzz_target;
use lazy_static::lazy_static;

use sealvault_tools_lib::{InPageRequestContextMock, ToolAppCore};
use uniffi_sealvault_core::{InPageProvider};

lazy_static! {
    static ref RUNTIME: tokio::runtime::Runtime = {
        let cores = std::thread::available_parallelism().expect("can query cores");
        tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .max_blocking_threads(cores.into())
            .build()
            .unwrap()
    };

    static ref APP_CORE: ToolAppCore = {
        ToolAppCore::new().expect("app core initializes")
    };
}

const URL: &str = "https://example.com";

fuzz_target!(|raw_request: String| {
    let resources = APP_CORE.core.resources();
    let context = Box::new(InPageRequestContextMock::new(URL));
    let provider = InPageProvider::new(resources, context).expect("valid url");
    let _ = RUNTIME.block_on(provider.in_page_request_async(raw_request));
});
