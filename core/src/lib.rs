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

mod backup;
mod db;
mod device;
mod encryption;
mod error;
mod favicon;
mod http_client;
mod public_suffix_list;
mod resources;
mod signatures;
mod ui_callback;
mod utils;

// Interfaces defined in SealVaultCore.udl must be exposed directly.
pub use crate::{
    app_core::{
        AppCore, CoreArgs, EthChangeDappChainArgs, EthTransferFungibleTokenArgs,
        EthTransferNativeTokenArgs,
    },
    async_runtime::{block_on, handle},
    backup::{
        find_latest_backup as core_find_latest_backup,
        restore_backup as core_restore_backup, BackupError as CoreBackupError,
        BackupRestoreData, BackupStorageI as CoreBackupStorageI,
    },
    dto::{
        CoreAddress, CoreDapp, CoreError, CoreEthChain, CoreFungibleToken, CoreNFT,
        CoreProfile, CoreTokens,
    },
    error::Error,
    in_page_provider::{
        CoreInPageCallbackI, DappApprovalParams, InPageProvider, InPageRequestContextI,
    },
    protocols::FungibleTokenType,
    ui_callback::{
        CoreUICallbackI, DappAllotmentTransferResult, DappSignatureResult,
        DappTransactionApproved, DappTransactionResult, TokenTransferResult,
    },
    utils::uri_fixup as core_uri_fixup,
};

// Build FFI based on SealVaultCore.udl.
uniffi_macros::include_scaffolding!("SealVaultCore");
