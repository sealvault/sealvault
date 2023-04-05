// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use ethers::prelude::U256;

use crate::protocols::eth::{token, ChainId, ChecksumAddress, NativeTokenAmount};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FungibleTokenBalance {
    pub chain_id: ChainId,
    pub contract_address: ChecksumAddress,
    pub amount: U256,
    pub decimals: u8,
    pub symbol: String,
    pub name: String,
    pub logo: Option<url::Url>,
}

impl FungibleTokenBalance {
    pub fn display_amount(&self) -> String {
        token::display_amount(self.amount, self.decimals)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct NFTBalance {
    pub chain_id: ChainId,
    pub contract_address: ChecksumAddress,
    pub symbol: String,
    pub collection_name: String,
    pub name: String,
    pub token_id: String,
    pub image_url: Option<url::Url>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TokenBalances {
    pub chain_id: ChainId,
    pub native_token: NativeTokenAmount,
    pub fungible_tokens: Vec<FungibleTokenBalance>,
    pub nfts: Vec<NFTBalance>,
}

impl TokenBalances {
    pub fn default_for_chain(chain_id: ChainId) -> Self {
        TokenBalances {
            chain_id,
            native_token: NativeTokenAmount::zero_balance(chain_id),
            fungible_tokens: Vec::new(),
            nfts: Vec::new(),
        }
    }
}
