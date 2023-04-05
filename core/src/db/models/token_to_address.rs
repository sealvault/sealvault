// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use aead::consts::U2;
use generic_array::GenericArray;

use crate::{
    db::{
        deterministic_id::{DeriveDeterministicId, EntityName},
        models::AddressId,
        schema::tokens_to_addresses,
        DeterministicId,
    },
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
#[diesel(table_name = tokens_to_addresses)]
pub struct TokenToAddress {
    pub deterministic_id: DeterministicId,
    pub address_id: DeterministicId,
    pub chain_id: DeterministicId,
    pub created_at: String,
    pub updated_at: Option<String>,
}

pub struct TokenToAddressEntity<'a> {
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
pub struct NewTokenToAddressEntity<'a> {
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
