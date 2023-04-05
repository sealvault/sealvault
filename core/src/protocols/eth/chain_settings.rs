// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use core_macros::sql_json;
use diesel::sql_types::Text;
use serde::{Deserialize, Serialize};

use crate::protocols::eth::NativeTokenAmount;

/// User settings for an Ethereum chain
#[derive(
    Clone, Debug, PartialEq, Eq, Serialize, Deserialize, AsExpression, FromSqlRow,
)]
#[diesel(sql_type = Text)]
pub struct ChainSettings {
    pub default_dapp_allotment: NativeTokenAmount,
}

sql_json!(ChainSettings);

impl ChainSettings {
    pub fn new(default_dapp_allotment: NativeTokenAmount) -> Self {
        Self {
            default_dapp_allotment,
        }
    }
}
