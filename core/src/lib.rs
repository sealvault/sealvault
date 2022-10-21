// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

#![feature(slice_take)]

#[macro_use]
extern crate diesel;
extern crate lazy_static;
#[macro_use]
extern crate num_derive;

// These are public, because they're used by the dev server
pub mod app_core;
pub mod assets;
pub mod async_runtime;
pub mod config;
pub mod dto;
pub mod in_page_provider;
pub mod protocols;

mod db;
mod encryption;
mod error;
mod favicon;
mod http_client;
mod public_suffix_list;
mod signatures;
mod ui_callback;
mod utils;

// Interfaces defined in SealVaultCore.udl must be exposed directly.
pub use crate::{
    app_core::{AppCore, CoreArgs},
    dto::{CoreAccount, CoreAddress, CoreDapp, CoreError, CoreEthChain, CoreToken},
    error::Error,
    in_page_provider::{CoreInPageCallbackI, DappApprovalParams, InPageRequestContextI},
    protocols::TokenType,
    ui_callback::{CoreUICallbackI, DappAllotmentTransferResult},
    utils::uri_fixup,
};

// Build FFI based on SealVaultCore.udl.
uniffi_macros::include_scaffolding!("SealVaultCore");
