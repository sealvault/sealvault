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
pub mod assets;
pub mod async_runtime;
pub mod config;
pub mod in_page_provider;

pub mod app_core;
mod db;
pub mod dto;
mod encryption;
mod error;
mod favicon;
mod http_client;
pub mod protocols;
mod public_suffix_list;
mod signatures;
mod utils;

// Interfaces defined in SealVaultCore.udl must be exposed directly.
pub use crate::app_core::{AppCore, CoreArgs};
pub use crate::dto::{CoreAccount, CoreAddress, CoreDapp, CoreError, CoreToken};
pub use crate::error::Error;
pub use crate::in_page_provider::{
    CoreInPageCallbackI, DappApprovalParams, InPageRequestContextI,
};
pub use crate::protocols::TokenType;
pub use crate::utils::uri_fixup;

// Build FFI based on SealVaultCore.udl.
uniffi_macros::include_scaffolding!("SealVaultCore");
