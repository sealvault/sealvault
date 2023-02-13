// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use url::Url;

use crate::{
    protocols::eth::{ChainId, ChecksumAddress},
    Error,
};

/// Get the blockchain explorer url for an address.
pub fn address_url(chain_id: ChainId, address: ChecksumAddress) -> Result<Url, Error> {
    chain_id
        .explorer_url()
        .join(&format!("address/{}", address))
        .map_err(map_err)
}

pub fn tx_url(chain_id: ChainId, tx_hash: &str) -> Result<Url, Error> {
    chain_id
        .explorer_url()
        .join(&format!("tx/{}", tx_hash))
        .map_err(map_err)
}

// We don't want always want to map parse error automatically, hence no `From` implementation.
fn map_err(err: url::ParseError) -> Error {
    // Parse error has static messages, OK to expose.
    Error::Fatal {
        error: err.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;

    #[test]
    fn correct_ethereum_explorer_address_url() -> Result<()> {
        let address = "0xd8f3059Ba60f8253977Fe6731C3e54aBFF368c48";
        let url = address_url(ChainId::EthMainnet, address.parse()?)?;
        assert_eq!(
            url.as_str(),
            "https://etherscan.io/address/0xd8f3059Ba60f8253977Fe6731C3e54aBFF368c48"
        );
        Ok(())
    }

    #[test]
    fn correct_ethereum_explorer_tx_hash_url() -> Result<()> {
        let tx_hash =
            "0xd373966d03308bda2f6b8009dbd0e15ddfce2a7bdfcc067ed4dae7f41faa262e";
        let url = tx_url(ChainId::EthMainnet, tx_hash)?;
        assert_eq!(url.as_str(), "https://etherscan.io/tx/0xd373966d03308bda2f6b8009dbd0e15ddfce2a7bdfcc067ed4dae7f41faa262e");
        Ok(())
    }
}
