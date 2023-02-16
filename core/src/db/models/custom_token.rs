// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::{prelude::*, SqliteConnection};
use generic_array::{typenum::U3, GenericArray};

use crate::{
    db::{
        deterministic_id::{DeriveDeterministicId, DeterministicId, EntityName},
        models as m,
        schema::custom_tokens,
        DeferredTxConnection,
    },
    protocols::{eth, TokenType},
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
pub struct CustomToken {
    pub deterministic_id: DeterministicId,
    pub address: eth::ChecksumAddress,
    pub chain_id: DeterministicId,
    pub type_: TokenType,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl CustomToken {
    pub fn create_eth_token(
        tx_conn: &mut DeferredTxConnection,
        contract_address: eth::ChecksumAddress,
        chain_id: eth::ChainId,
        token_type: TokenType,
    ) -> Result<(), Error> {
        let chain_db_id = m::Chain::fetch_or_create_eth_chain_id(tx_conn, chain_id)?;
        let entity = CustomTokenEntity {
            address: &contract_address,
            chain_id: &chain_db_id,
            type_: &token_type,
        };
        entity.insert(tx_conn.as_mut())
    }
}

#[derive(Insertable)]
#[diesel(table_name = custom_tokens)]
#[readonly::make]
struct CustomTokenEntity<'a> {
    pub address: &'a eth::ChecksumAddress,
    pub chain_id: &'a DeterministicId,
    pub type_: &'a TokenType,
}

impl<'a> CustomTokenEntity<'a> {
    fn insert(&self, conn: &mut SqliteConnection) -> Result<(), Error> {
        use custom_tokens::dsl as ct;

        let created_at = rfc3339_timestamp();
        let deterministic_id = self.deterministic_id()?;

        diesel::insert_into(custom_tokens::table)
            .values((
                self,
                ct::deterministic_id.eq(&deterministic_id),
                ct::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(())
    }
}

impl<'a> DeriveDeterministicId<'a, &'a [u8], U3> for CustomTokenEntity<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::CustomToken
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
