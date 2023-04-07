// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
mod native;
mod token_balances;

use std::collections::HashMap;

use futures::StreamExt;
use strum::IntoEnumIterator;
pub use token_balances::{FungibleTokenBalance, NFTBalance, TokenBalances};

use crate::{
    db::models as m,
    protocols::eth::{
        ankr::AnkrApi, token_api::native::NativeTokenAPi, ChainId, RpcManagerI,
    },
    Error,
};

pub async fn fetch_token_balances(
    rpc_manager: &dyn RpcManagerI,
    tokens_for_address: m::EthTokensForAddress,
) -> Result<Vec<TokenBalances>, Error> {
    let m::EthTokensForAddress {
        address,
        fungible_tokens,
        ..
    } = tokens_for_address;

    let fungible_tokens_by_api = fungible_tokens.into_iter().fold(
        HashMap::new(),
        |mut acc, (chain_id, contract_addresses)| {
            let api = TokenApi::for_chain(chain_id);
            acc.entry(api)
                .or_insert_with(HashMap::new)
                .insert(chain_id, contract_addresses);
            acc
        },
    );

    let results = futures::stream::iter(fungible_tokens_by_api.into_iter())
        .map(|(api, fungible_tokens)| async move {
            let result = match api {
                TokenApi::Ankr => {
                    let ankr = AnkrApi::new()?;
                    ankr.fetch_token_balances(address).await?
                }
                TokenApi::Native => {
                    let native = NativeTokenAPi::new(rpc_manager);
                    native
                        .fetch_token_balances(address, fungible_tokens)
                        .await?
                }
            };
            Ok::<_, Error>(result)
        })
        .buffered(TokenApi::iter().len())
        .collect::<Vec<Result<Vec<_>, Error>>>()
        .await
        .into_iter()
        .collect::<Result<Vec<Vec<_>>, Error>>()?;

    Ok(results.into_iter().flatten().collect())
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
        }
    }
}
