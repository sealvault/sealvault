// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::prelude::*;
use generic_array::{
    typenum::{U2, U3},
    GenericArray,
};

use crate::{
    db::{
        deterministic_id::{DeriveDeterministicId, DeterministicId, EntityName},
        models as m,
        models::AddressId,
        schema::{tokens, tokens_to_addresses},
        DeferredTxConnection,
    },
    protocols::{eth, TokenType},
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
pub struct Token {
    pub deterministic_id: DeterministicId,
    pub identifier: eth::ChecksumAddress,
    pub chain_id: DeterministicId,
    pub type_: TokenType,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl Token {
    /// Assumes there is already an address (possibly) for the chain in the DB.
    pub fn upsert_tokens(
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

            diesel::insert_into(tokens::table)
                .values(&token)
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
        })
    }
}

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

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
#[diesel(table_name = tokens_to_addresses)]
struct TokenToAddress {
    pub deterministic_id: DeterministicId,
    pub address_id: DeterministicId,
    pub chain_id: DeterministicId,
    pub created_at: String,
    pub updated_at: Option<String>,
}

#[readonly::make]
struct TokenToAddressEntity<'a> {
    pub token_id: &'a DeterministicId,
    pub address_id: &'a AddressId,
}

impl<'a> DeriveDeterministicId<'a, &'a str, U2> for TokenToAddressEntity<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::TokenToAddress
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U2> {
        [self.token_id.as_ref(), self.address_id.as_ref()].into()
    }
}

#[derive(Insertable)]
#[diesel(table_name = tokens_to_addresses)]
struct NewTokenToAddressEntity<'a> {
    deterministic_id: DeterministicId,
    token_id: &'a DeterministicId,
    address_id: &'a AddressId,
    created_at: String,
}

impl<'a> TryFrom<TokenToAddressEntity<'a>> for NewTokenToAddressEntity<'a> {
    type Error = Error;

    fn try_from(value: TokenToAddressEntity<'a>) -> Result<Self, Self::Error> {
        let deterministic_id = value.deterministic_id()?;
        let TokenToAddressEntity {
            token_id,
            address_id,
        } = value;
        Ok(Self {
            deterministic_id,
            token_id,
            address_id,
            created_at: rfc3339_timestamp(),
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use anyhow::Result;

    use super::*;
    use crate::app_core::tests::TmpCore;

    impl Token {
        pub fn list_all(conn: &mut SqliteConnection) -> Result<Vec<Self>, Error> {
            Ok(tokens::table.load::<Self>(conn)?)
        }
    }

    impl TokenToAddress {
        pub fn list_all(conn: &mut SqliteConnection) -> Result<Vec<Self>, Error> {
            Ok(tokens_to_addresses::table.load::<Self>(conn)?)
        }
    }

    #[test]
    fn upsert_token_balances() -> Result<()> {
        let tmp_core = TmpCore::new()?;
        let wallet = tmp_core.first_profile_wallet();
        let owner_address: eth::ChecksumAddress = wallet.checksum_address.parse()?;
        let chain_id = eth::ChainId::PolygonMumbai;
        let native_token = eth::NativeTokenAmount::zero_balance(chain_id);
        let fungible_tokens = vec![eth::FungibleTokenBalance {
            chain_id,
            contract_address: "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48".parse()?,
            amount: Default::default(),
            decimals: 0,
            symbol: "".to_string(),
            name: "".to_string(),
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
                Token::upsert_tokens(&mut tx_conn, &token_balances, &address_id)
            })?;

        token_balances.nfts = vec![eth::NFTBalance {
            chain_id,
            contract_address: "0xb47e3cd837dDF8e4c57F05d70Ab865de6e193BBB".parse()?,
            symbol: "".to_string(),
            collection_name: "".to_string(),
            name: "".to_string(),
            token_id: "".to_string(),
            image_url: None,
        }];

        tmp_core
            .connection_pool()
            .deferred_transaction(|mut tx_conn| {
                Token::upsert_tokens(&mut tx_conn, &token_balances, &address_id)
            })?;

        let mut conn = tmp_core.connection_pool().connection()?;
        let tokens = Token::list_all(&mut conn)?;
        let tokens_to_addresses = TokenToAddress::list_all(&mut conn)?;
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens_to_addresses.len(), 2);
        let token_types: HashSet<TokenType> = tokens.iter().map(|t| t.type_).collect();
        assert_eq!(token_types.len(), 2);

        Ok(())
    }
}
