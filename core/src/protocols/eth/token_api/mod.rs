// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
mod native;
mod token_balances;

use std::collections::HashMap;

pub use token_balances::{FungibleTokenBalance, NFTBalance, TokenBalances};

use crate::{
    db::models as m,
    protocols::eth::{
        ankr::{AnkrApi, AnkrBlockchain},
        token_api::native::NativeTokenAPi,
        ChainId, RpcManagerI,
    },
    Error,
};

pub async fn fetch_token_balances(
    rpc_manager: &dyn RpcManagerI,
    tokens_for_address: m::EthTokensForAddress,
) -> Result<Vec<TokenBalances>, Error> {
    let m::EthTokensForAddress {
        address,
        native_tokens,
        fungible_tokens,
        ..
    } = tokens_for_address;

    // Always fetch from Ankr API for discovery.
    let ankr_api = AnkrApi::new(rpc_manager).await?;
    let ankr_future = ankr_api.fetch_token_balances(address);

    // Fetch tokens through native API that aren't supported by Ankr
    let native_api_native_tokens = native_tokens
        .into_iter()
        .filter(|chain_id| !AnkrBlockchain::supported(*chain_id))
        .collect::<Vec<_>>();
    let native_api_fungible_tokens: HashMap<_, _> = fungible_tokens
        .into_iter()
        .filter(|(chain_id, _)| TokenApi::for_chain(*chain_id) == TokenApi::Native)
        .collect();
    let native_api = NativeTokenAPi::new(rpc_manager);
    let native_future = native_api.fetch_token_balances(
        address,
        native_api_native_tokens,
        native_api_fungible_tokens,
    );

    let (ankr_res, native_res) = futures::join!(ankr_future, native_future);
    let mut ankr_items = ankr_res
        .map_err(|err| {
            log::error!("Error fetching tokens from Ankr API: '{err}'");
            err
        })
        .unwrap_or_default();
    let mut native_items = native_res
        .map_err(|err| {
            log::error!("Error fetching tokens from native API: '{err}'");
            err
        })
        .unwrap_or_default();
    ankr_items.append(&mut native_items);
    Ok(ankr_items)
}

#[derive(Debug, Eq, PartialEq, Hash, strum_macros::EnumIter)]
enum TokenApi {
    Ankr,
    Native,
}

impl TokenApi {
    fn for_chain(chain_id: ChainId) -> Self {
        match chain_id {
            ChainId::EthMainnet => Self::Ankr,
            ChainId::EthGoerli => Self::Ankr,
            ChainId::PolygonMainnet => Self::Ankr,
            ChainId::PolygonMumbai => Self::Ankr,
            ChainId::FilecoinHyperspaceTestnet => Self::Native,
            ChainId::ZkSync => Self::Native,
            ChainId::ZkSyncTestnet => Self::Native,
        }
    }
}
