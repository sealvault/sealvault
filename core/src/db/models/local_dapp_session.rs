// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::db::schema::{
    accounts, addresses, asymmetric_keys, chains, dapps, local_dapp_sessions,
};
use crate::db::{DeferredTxConnection, JsonValue};

use crate::Error;
use diesel::prelude::*;

use crate::db::models as m;

use crate::protocols::eth;
use crate::utils::rfc3339_timestamp;
use typed_builder::TypedBuilder;

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
pub struct LocalDappSession {
    pub id: i64,
    pub address_id: String,
    pub dapp_id: String,
    pub last_used_at: String,
    pub created_at: String,
}

#[derive(TypedBuilder)]
#[readonly::make]
pub struct DappSessionParams<'a> {
    pub dapp_id: &'a str,
    pub account_id: &'a str,
    #[builder(default)]
    pub chain_id: Option<eth::ChainId>,
}

impl LocalDappSession {
    /// Fetch the currently used address for a local dapp session or create a new session.
    /// Assumes address exists already.
    pub fn create_eth_session_if_not_exists(
        tx_conn: &mut DeferredTxConnection,
        params: &DappSessionParams,
    ) -> Result<m::Address, Error> {
        let maybe_address = Self::fetch_eth_session_address(tx_conn, params)?;
        let address = if let Some(address) = maybe_address {
            address
        } else {
            Self::create_eth_session(tx_conn, params)?
        };
        Ok(address)
    }

    /// Create an Ethereum dapp session on default dapp chain for account and returns the address.
    /// Assumes address already exists and that there is one dapp key per account.
    pub fn create_eth_session(
        tx_conn: &mut DeferredTxConnection,
        params: &DappSessionParams,
    ) -> Result<m::Address, Error> {
        use accounts::dsl as ac;
        use addresses::dsl as ad;
        use asymmetric_keys::dsl as ak;
        use chains as c;
        use dapps::dsl as d;
        use local_dapp_sessions::dsl as lds;

        let chain_id = params
            .chain_id
            .unwrap_or_else(eth::ChainId::default_dapp_chain);
        let protocol_data: JsonValue =
            JsonValue::convert_from(eth::ProtocolData::new(chain_id))?;

        // This assumes one dapp key per account.
        let address: m::Address = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(ad::asymmetric_key_id)),
            )
            .inner_join(accounts::table.on(ac::deterministic_id.eq(ak::account_id)))
            .inner_join(dapps::table.on(d::deterministic_id.nullable().eq(ak::dapp_id)))
            .inner_join(chains::table.on(c::deterministic_id.eq(ad::chain_id)))
            .filter(ac::deterministic_id.eq(params.account_id))
            .filter(d::deterministic_id.eq(params.dapp_id))
            .filter(c::protocol_data.eq(&protocol_data))
            .select(m::Address::all_columns())
            .first::<m::Address>(tx_conn.as_mut())?;

        let created_at = rfc3339_timestamp();

        diesel::insert_into(local_dapp_sessions::table)
            .values((
                lds::address_id.eq(&*address.deterministic_id),
                lds::dapp_id.eq(params.dapp_id),
                lds::created_at.eq(&created_at),
                lds::last_used_at.eq(&created_at),
            ))
            .execute(tx_conn.as_mut())?;

        Ok(address)
    }

    /// Fetch currently used address for a dapp session.
    fn fetch_eth_session_address(
        tx_conn: &mut DeferredTxConnection,
        params: &DappSessionParams,
    ) -> Result<Option<m::Address>, Error> {
        use accounts::dsl as ac;
        use addresses::dsl as ad;
        use asymmetric_keys::dsl as ak;
        use local_dapp_sessions::dsl as lds;

        let address: Option<m::Address> = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(ad::asymmetric_key_id)),
            )
            .inner_join(accounts::table.on(ac::deterministic_id.eq(ak::account_id)))
            .inner_join(
                local_dapp_sessions::table.on(lds::address_id.eq(ad::deterministic_id)),
            )
            .filter(ac::deterministic_id.eq(params.account_id))
            .filter(lds::dapp_id.eq(params.dapp_id))
            .select(m::Address::all_columns())
            .first(tx_conn.as_mut())
            .optional()?;

        if let Some(address) = address.as_ref() {
            diesel::update(
                local_dapp_sessions::table
                    .filter(lds::address_id.eq(&*address.deterministic_id)),
            )
            .set(lds::last_used_at.eq(rfc3339_timestamp()))
            .execute(tx_conn.as_mut())?;
        }

        Ok(address)
    }

    /// Update currently used address for a dapp session.
    pub fn update_session_address(
        tx_conn: &mut DeferredTxConnection,
        params: &UpdateDappSessionParams,
    ) -> Result<(), Error> {
        use local_dapp_sessions::dsl as lds;

        let old_key_id =
            m::Address::fetch_key_id(tx_conn.as_mut(), params.old_address_id)?;
        let new_key_id =
            m::Address::fetch_key_id(tx_conn.as_mut(), params.new_address_id)?;
        if old_key_id != new_key_id {
            return Err(Error::Fatal {
                error: "Assumed same key for dapp session change".into(),
            });
        }

        // There is a unique constraint on address
        diesel::update(
            local_dapp_sessions::table.filter(lds::address_id.eq(params.old_address_id)),
        )
        .set(lds::address_id.eq(params.new_address_id))
        .execute(tx_conn.as_mut())?;

        Ok(())
    }

    /// Fetch currently used chain id for a dapp session.
    pub fn fetch_eth_chain_id(
        conn: &mut SqliteConnection,
        params: &DappSessionParams,
    ) -> Result<eth::ChainId, Error> {
        use accounts::dsl as ac;
        use addresses::dsl as ad;
        use asymmetric_keys::dsl as ak;
        use chains as c;
        use local_dapp_sessions::dsl as lds;

        // TODO avoid join + filter copy pasta
        let protocol_data_json: JsonValue = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(ad::asymmetric_key_id)),
            )
            .inner_join(accounts::table.on(ac::deterministic_id.eq(ak::account_id)))
            .inner_join(
                local_dapp_sessions::table.on(lds::address_id.eq(ad::deterministic_id)),
            )
            .inner_join(chains::table.on(c::deterministic_id.eq(ad::chain_id)))
            .filter(ac::deterministic_id.eq(params.account_id))
            .filter(lds::dapp_id.eq(params.dapp_id))
            .select(c::protocol_data)
            .first::<JsonValue>(conn)?;
        let protocol_data: eth::ProtocolData = protocol_data_json.convert_into()?;

        Ok(protocol_data.chain_id)
    }
}

#[derive(TypedBuilder, Debug, Clone, Eq, PartialEq)]
#[readonly::make]
pub struct UpdateDappSessionParams<'a> {
    old_address_id: &'a str,
    new_address_id: &'a str,
}
