// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use typed_builder::TypedBuilder;

pub trait CoreUICallbackI: Send + Sync + Debug {
    /// Whether the default dapp allotment was successfully transferred after adding a dapp.
    fn dapp_allotment_transfer_result(&self, result: DappAllotmentTransferResult);
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
