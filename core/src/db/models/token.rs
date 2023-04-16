// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::collections::HashMap;

use core_macros::{deterministic_id, sql_text};
use derive_more::{AsRef, Display, Into};
use diesel::prelude::*;
use generic_array::{typenum::U3, GenericArray};

use crate::{
    db::{
        deterministic_id::{DeriveDeterministicId, DeterministicId, EntityName},
        models as m,
        models::{
            token_to_address::{NewTokenToAddressEntity, TokenToAddressEntity},
            AddressId,
        },
        schema::{addresses, chains, tokens, tokens_to_addresses},
        DeferredTxConnection,
    },
    protocols::{eth, BlockchainProtocol, TokenType},
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
pub struct Token {
    pub deterministic_id: TokenId,
    pub identifier: eth::ChecksumAddress,
    pub chain_id: DeterministicId,
    pub type_: TokenType,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl Token {
    pub fn upsert_token(
        tx_conn: &mut DeferredTxConnection,
        address_id: &AddressId,
        chain_id: eth::ChainId,
        contract_address: eth::ChecksumAddress,
        token_type: TokenType,
    ) -> Result<(), Error> {
        let chain_db_id = m::Chain::fetch_or_create_eth_chain_id(tx_conn, chain_id)?;
        let new_token: NewTokenEntity = TokenEntity {
            address: &contract_address,
            chain_id: &chain_db_id,
            type_: token_type,
        }
        .try_into()?;

        Self::upsert_token_inner(tx_conn, address_id, &new_token)
    }

    pub fn upsert_token_balances(
        tx_conn: &mut DeferredTxConnection,
        token_balances: &eth::TokenBalances,
        address_id: &AddressId,
    ) -> Result<(), Error> {
        let chain_db_id =
            m::Chain::fetch_or_create_eth_chain_id(tx_conn, token_balances.chain_id)?;

        let fungible_tokens =
            token_balances.fungible_tokens.iter().map(|fungible_token| {
                let new_token: Result<NewTokenEntity, Error> = TokenEntity {
                    address: &fungible_token.contract_address,
                    chain_id: &chain_db_id,
                    type_: TokenType::Fungible,
                }
                .try_into();
                new_token
            });
        let nfts = token_balances.nfts.iter().map(|nft| {
            let new_token: Result<NewTokenEntity, Error> = TokenEntity {
                address: &nft.contract_address,
                chain_id: &chain_db_id,
                type_: TokenType::Nft,
            }
            .try_into();
            new_token
        });

        fungible_tokens.chain(nfts).try_for_each(|token| {
            let token = token?;
            Self::upsert_token_inner(tx_conn, address_id, &token)
        })
    }

    fn upsert_token_inner(
        tx_conn: &mut DeferredTxConnection,
        address_id: &AddressId,
        token: &NewTokenEntity,
    ) -> Result<(), Error> {
        diesel::insert_into(tokens::table)
            .values(token)
            .on_conflict_do_nothing()
            .execute(tx_conn.as_mut())?;

        let token_to_address: NewTokenToAddressEntity = TokenToAddressEntity {
            token_id: &token.deterministic_id,
            address_id,
        }
        .try_into()?;

        diesel::insert_into(tokens_to_addresses::table)
            .values(token_to_address)
            .on_conflict_do_nothing()
            .execute(tx_conn.as_mut())?;
        Ok(())
    }

    pub fn eth_tokens_for_address(
        tx_conn: &mut DeferredTxConnection,
        address: eth::ChecksumAddress,
    ) -> Result<EthTokensForAddress, Error> {
        use addresses::dsl as a;
        use chains::dsl as c;
        use tokens::dsl as t;
        use tokens_to_addresses::dsl as tta;

        let native_tokens =
            m::Address::fetch_eth_chains_for_address(tx_conn.as_mut(), address)?;

        let rows = addresses::table
            .inner_join(chains::table.on(a::chain_id.eq(c::deterministic_id)))
            .inner_join(
                tokens_to_addresses::table.on(a::deterministic_id.eq(tta::address_id)),
            )
            .inner_join(tokens::table.on(tta::token_id.eq(t::deterministic_id)))
            .filter(a::address.eq(address))
            .filter(c::protocol.eq(BlockchainProtocol::Ethereum))
            .select((c::protocol_data, t::address, t::type_))
            .load::<(eth::ProtocolData, eth::ChecksumAddress, TokenType)>(
                tx_conn.as_mut(),
            )?;

        let mut result = EthTokensForAddress::new(address, native_tokens);
        for (protocol_data, contract_address, token_type) in rows {
            let chain_id: eth::ChainId = protocol_data.into();
            let entry = match token_type {
                TokenType::Fungible => result.fungible_tokens.entry(chain_id),
                TokenType::Nft => result.nfts.entry(chain_id),
            }
            .or_default();
            entry.push(contract_address)
        }

        Ok(result)
    }
}

#[derive(
    Debug,
    Display,
    Clone,
    Eq,
    PartialEq,
    PartialOrd,
    Ord,
    Hash,
    Into,
    AsRef,
    AsExpression,
    FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Text)]
#[as_ref(forward)]
#[repr(transparent)]
pub struct TokenId(String);

deterministic_id!(TokenId);
sql_text!(TokenId);

#[readonly::make]
struct TokenEntity<'a> {
    pub address: &'a eth::ChecksumAddress,
    pub chain_id: &'a DeterministicId,
    pub type_: TokenType,
}

impl<'a> DeriveDeterministicId<'a, &'a [u8], U3> for TokenEntity<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::Token
    }

    fn unique_columns(&'a self) -> GenericArray<&'a [u8], U3> {
        let token_type: &'static str = self.type_.into();
        [
            self.address.as_ref(),
            self.chain_id.as_ref(),
            token_type.as_ref(),
        ]
        .into()
    }
}

#[derive(Insertable)]
#[diesel(table_name = tokens)]
struct NewTokenEntity<'a> {
    deterministic_id: DeterministicId,
    address: &'a eth::ChecksumAddress,
    chain_id: &'a DeterministicId,
    type_: TokenType,
    created_at: String,
}

impl<'a> TryFrom<TokenEntity<'a>> for NewTokenEntity<'a> {
    type Error = Error;

    fn try_from(value: TokenEntity<'a>) -> Result<Self, Self::Error> {
        let deterministic_id = value.deterministic_id()?;
        let TokenEntity {
            address,
            chain_id,
            type_,
        } = value;
        Ok(Self {
            deterministic_id,
            address,
            chain_id,
            type_,
            created_at: rfc3339_timestamp(),
        })
    }
}

#[derive(Debug, Clone)]
pub struct EthTokensForAddress {
    /// The owner address.
    pub address: eth::ChecksumAddress,
    /// Chain ids where the address can have native tokens.
    pub native_tokens: Vec<eth::ChainId>,
    /// Map of chain id to contract addresses for fungible tokens.
    pub fungible_tokens: HashMap<eth::ChainId, Vec<eth::ChecksumAddress>>,
    /// Map of chain id to contract addresses for nfts.
    pub nfts: HashMap<eth::ChainId, Vec<eth::ChecksumAddress>>,
}

impl EthTokensForAddress {
    fn new(address: eth::ChecksumAddress, native_tokens: Vec<eth::ChainId>) -> Self {
        Self {
            address,
            native_tokens,
            fungible_tokens: Default::default(),
            nfts: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {

    use anyhow::Result;

    use super::*;
    use crate::app_core::tests::TmpCore;

    #[test]
    fn upsert_token_balances() -> Result<()> {
        let tmp_core = TmpCore::new()?;
        let wallet = tmp_core.first_profile_wallet();
        let owner_address: eth::ChecksumAddress = wallet.checksum_address.parse()?;
        let chain_id = eth::ChainId::PolygonMumbai;
        let native_token = eth::NativeTokenAmount::zero_balance(chain_id);
        let fungible_token_address: eth::ChecksumAddress =
            "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48".parse()?;
        let fungible_tokens = vec![eth::FungibleTokenBalance {
            chain_id,
            contract_address: fungible_token_address,
            amount: Default::default(),
            decimals: 0,
            symbol: "".to_string(),
            logo: None,
        }];

        let address_id = tmp_core
            .connection_pool()
            .deferred_transaction(|mut tx_conn| {
                m::Address::fetch_or_create_id_by_address_on_chain(
                    &mut tx_conn,
                    owner_address,
                    chain_id,
                )
            })?
            .expect("address is in DB");

        let mut token_balances = eth::TokenBalances {
            chain_id,
            native_token,
            fungible_tokens,
            nfts: Default::default(),
        };

        tmp_core
            .connection_pool()
            .deferred_transaction(|mut tx_conn| {
                Token::upsert_token_balances(&mut tx_conn, &token_balances, &address_id)
            })?;

        let nft_address: eth::ChecksumAddress =
            "0xb47e3cd837dDF8e4c57F05d70Ab865de6e193BBB".parse()?;
        token_balances.nfts = vec![eth::NFTBalance {
            chain_id,
            contract_address: nft_address,
            symbol: "".to_string(),
            collection_name: "".to_string(),
            name: "".to_string(),
            token_id: "".to_string(),
            image_url: None,
        }];

        tmp_core
            .connection_pool()
            .deferred_transaction(|mut tx_conn| {
                Token::upsert_token_balances(&mut tx_conn, &token_balances, &address_id)
            })?;

        let tokens = tmp_core
            .connection_pool()
            .deferred_transaction(|mut tx_conn| {
                let address = m::Address::fetch_address(tx_conn.as_mut(), &address_id)?;
                Token::eth_tokens_for_address(&mut tx_conn, address)
            })?;

        let fungible_token_addresses = tokens.fungible_tokens.get(&chain_id).unwrap();
        assert_eq!(fungible_token_addresses.len(), 1);
        assert_eq!(fungible_token_addresses[0], fungible_token_address);
        let nft_addresses = tokens.nfts.get(&chain_id).unwrap();
        assert_eq!(nft_addresses.len(), 1);
        assert_eq!(nft_addresses[0], nft_address);

        Ok(())
    }
}
