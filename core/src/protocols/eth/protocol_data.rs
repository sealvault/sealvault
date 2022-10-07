// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use serde::{Deserialize, Serialize};

use crate::protocols::eth::chain_id::ChainId;

/// Information about the
#[derive(Debug, Clone, Serialize, Deserialize)]
#[readonly::make]
pub struct ProtocolData {
    pub chain_id: ChainId,
}

impl ProtocolData {
    pub fn new(chain_id: ChainId) -> Self {
        Self { chain_id }
    }
}

impl From<ChainId> for ProtocolData {
    fn from(chain_id: ChainId) -> Self {
        Self::new(chain_id)
    }
}
