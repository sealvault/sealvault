// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::collections::HashMap;

use url::Url;

use crate::{
    assets::load_asset_as_string,
    config::ETH_COMMON_TOKENS,
    protocols::eth::{ChainId, ChecksumAddress},
    Error,
};

#[derive(Debug, serde::Deserialize, serde::Serialize)]
pub struct CommonTokens {
    /// The commit hash of https://github.com/sealvault/assets from which the tokens were compiled
    pub commit_hash: String,
    /// The common fungible tokens for each chain
    pub fungible_tokens: HashMap<ChainId, Vec<CommonTokenInfo>>,
}

impl CommonTokens {
    pub(super) fn from_assets() -> Result<Self, Error> {
        let s = load_asset_as_string(ETH_COMMON_TOKENS)?;
        serde_json::from_str(&s).map_err(|_| Error::Fatal {
            error: "Failed to parse common tokens".to_string(),
        })
    }

    pub(super) fn contract_addresses_for_chain(
        &self,
        chain_id: ChainId,
    ) -> Vec<ChecksumAddress> {
        self.fungible_tokens
            .get(&chain_id)
            .map(|tokens| tokens.iter().map(|token| token.address).collect())
            .unwrap_or_default()
    }
}

#[derive(Debug, serde::Deserialize, serde::Serialize)]
pub struct CommonTokenInfo {
    pub address: ChecksumAddress,
    pub logo_uri: Option<Url>,
}

#[cfg(test)]
mod test {
    use anyhow::Result;
    use strum::IntoEnumIterator;

    use crate::protocols::eth::ChainId;

    #[test]
    fn test_common_tokens() -> Result<()> {
        let common_tokens = super::CommonTokens::from_assets()?;
        for chain_id in ChainId::iter() {
            if chain_id.trust_wallet_asset_name().is_some() {
                let tokens = common_tokens.fungible_tokens.get(&chain_id).unwrap();
                assert!(!tokens.is_empty());
            }
        }
        Ok(())
    }
}
