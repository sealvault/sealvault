// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use typed_builder::TypedBuilder;

pub trait CoreUICallbackI: Send + Sync + Debug {
    /// When a token transfer initiated by the user was sent to the blockchain API.
    fn sent_token_transfer(&self, result: TokenTransferResult);
    /// When a token transfer initiated by the user was confirmed or rejected.
    fn token_transfer_result(&self, result: TokenTransferResult);
    /// Whether the default dapp allotment was successfully transferred after adding a dapp.
    fn dapp_allotment_transfer_result(&self, result: DappAllotmentTransferResult);
    /// The in-page provider created an off-chain signature automatically for a dapp.
    fn signed_message_for_dapp(&self, result: DappSignatureResult);
    /// The in-page provider approved a transaction automatically for a dapp.
    fn approved_dapp_transaction(&self, result: DappTransactionApproved);
    /// The result of a transaction that was auto-approved by the in-page provider.
    fn dapp_transaction_result(&self, result: DappTransactionResult);
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct TokenTransferResult {
    /// The amount that was transferred.
    #[builder(setter(into))]
    pub amount: String,
    /// The symbol of the token that was transferred.
    #[builder(setter(into))]
    pub token_symbol: String,
    /// The displayable name of the chain where the token was transferred.
    #[builder(setter(into))]
    pub chain_display_name: String,
    /// The displayable name of the recepient (eg. account wallet, dapp domain or 0x... for
    /// external.
    #[builder(setter(into))]
    pub to_display_name: String,
    /// The transaction's explorer url. None on error or if the transaction isn't confirmed yet.
    #[builder(default = None)]
    pub explorer_url: Option<String>,
    /// Error message is none on success.
    #[builder(default = None)]
    pub error_message: Option<String>,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct DappAllotmentTransferResult {
    /// A human readable dapp identifier that can be presented to the user.
    #[builder(setter(into))]
    pub dapp_identifier: String,
    /// The amount that was transferred.
    #[builder(setter(into))]
    pub amount: String,
    /// The symbol of the token that was transferred.
    #[builder(setter(into))]
    pub token_symbol: String,
    /// The displayable name of the chain where the token was transferred.
    #[builder(setter(into))]
    pub chain_display_name: String,
    /// Error message is none on success.
    /// Uniffi doesn't support Result enum as argument unfortunately.
    #[builder(default = None)]
    pub error_message: Option<String>,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct DappSignatureResult {
    /// A human readable dapp identifier that can be presented to the user.
    #[builder(setter(into))]
    pub dapp_identifier: String,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct DappTransactionApproved {
    /// A human readable dapp identifier that can be presented to the user.
    #[builder(setter(into))]
    pub dapp_identifier: String,
    /// The displayable name of the chain where the transaction was approved.
    #[builder(setter(into))]
    pub chain_display_name: String,
}

#[derive(Clone, Debug, TypedBuilder)]
pub struct DappTransactionResult {
    /// A human readable dapp identifier that can be presented to the user.
    #[builder(setter(into))]
    pub dapp_identifier: String,
    #[builder(setter(into))]
    pub chain_display_name: String,
    /// The transaction's explorer url. None on error
    #[builder(default = None)]
    pub explorer_url: Option<String>,
    /// Error message is none on success.
    /// Uniffi doesn't support Result enum as argument unfortunately.
    #[builder(default = None)]
    pub error_message: Option<String>,
}
