// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use diesel::{prelude::*, SqliteConnection};
use generic_array::{typenum::U1, GenericArray};
use typed_builder::TypedBuilder;

use crate::{
    db::{
        deterministic_id::{DeterministicId, EntityName},
        models as m,
        schema::accounts,
        DeferredTxConnection,
    },
    encryption::Keychain,
    protocols::eth,
    utils::{new_uuid, rfc3339_timestamp},
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
pub struct Account {
    pub deterministic_id: String,
    pub uuid: String,
    pub name: String,
    pub picture_id: String,
    pub created_at: String,
    pub updated_at: Option<String>,
}

impl Account {
    pub fn list_all(conn: &mut SqliteConnection) -> Result<Vec<Account>, Error> {
        Ok(accounts::table.load::<Account>(conn)?)
    }

    /// Create a new account with Ethereum protocol wallet addresses and return the account's
    /// deterministic id.
    pub fn create_eth_account(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        params: &AccountParams,
    ) -> Result<String, Error> {
        let picture_id = m::AccountPicture::insert_bundled(
            tx_conn.as_mut(),
            params.bundled_picture_name,
        )?;
        let account_id = Self::insert(tx_conn.as_mut(), params.name, &picture_id)?;

        let mut chain_ids = eth::ChainId::default_wallet_chains().into_iter();
        let chain_id = chain_ids
            .next()
            .expect("there is at least one default chain id");
        let create_params = m::CreateEthAddressParams::builder()
            .account_id(&account_id)
            .chain_id(chain_id)
            .is_account_wallet(true)
            .build();

        let address_id =
            m::Address::create_eth_key_and_address(tx_conn, keychain, &create_params)?;
        let asymmetric_key_id = m::Address::fetch_key_id(tx_conn.as_mut(), &address_id)?;
        let address = m::Address::fetch_address(tx_conn.as_mut(), &address_id)?;

        // Create wallet addresses for the rest of the Ethereum chains
        for chain_id in chain_ids {
            m::NewAddress::builder()
                .asymmetric_key_id(&*asymmetric_key_id)
                .address(&*address)
                .build()
                .insert_eth(tx_conn, chain_id)?;
        }

        Ok(account_id)
    }

    /// Create a new account and return its deterministic id.
    fn insert(
        conn: &mut SqliteConnection,
        name: &str,
        picture_id: &str,
    ) -> Result<String, Error> {
        use accounts::dsl as a;

        let uuid = new_uuid();
        let entity = AccountEntity { uuid: &uuid };
        let deterministic_id = entity.deterministic_id()?;
        let created_at = rfc3339_timestamp();

        diesel::insert_into(accounts::table)
            .values((
                a::deterministic_id.eq(&deterministic_id),
                a::uuid.eq(&entity.uuid),
                a::name.eq(name),
                a::picture_id.eq(picture_id),
                a::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(deterministic_id)
    }
}

// Struct with typed builder ensures that arguments of same type aren't mixed up as Rust doesn't
// have named parameters.
#[derive(TypedBuilder)]
#[readonly::make]
pub struct AccountParams<'a> {
    #[builder(setter(into))]
    name: &'a str,
    #[builder(setter(into))]
    bundled_picture_name: &'a str,
}

struct AccountEntity<'a> {
    pub uuid: &'a str,
}

impl<'a> DeterministicId<'a, &'a str, U1> for AccountEntity<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::Account
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U1> {
        // When a user creates accounts on different devices those should be different entities,
        // hence the uuid as deterministic id.
        [self.uuid].into()
    }
}
