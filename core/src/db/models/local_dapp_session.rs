// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::prelude::*;
use typed_builder::TypedBuilder;

use crate::{
    db::{
        models as m,
        schema::{
            accounts, addresses, asymmetric_keys, chains, dapps, local_dapp_sessions,
        },
        DeferredTxConnection, JsonValue,
    },
    protocols::eth,
    utils::{new_uuid, rfc3339_timestamp},
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, TypedBuilder)]
pub struct LocalDappSession {
    pub uuid: String,
    pub address_id: String,
    pub dapp_id: String,

    pub chain_id: eth::ChainId,
    pub account_id: String,
    pub address: String,
}

#[derive(TypedBuilder)]
#[readonly::make]
pub struct DappSessionParams<'a> {
    pub dapp_id: &'a str,
    pub account_id: &'a str,
    #[builder(default = eth::ChainId::default_dapp_chain())]
    pub chain_id: eth::ChainId,
}

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(uuid))]
#[diesel(table_name = local_dapp_sessions)]
#[readonly::make]
struct LocalDappSessionEntity {
    uuid: String,
    address_id: String,
    dapp_id: String,
    last_used_at: String,
    created_at: String,
    updated_at: String,
}

type AllColumns = (
    local_dapp_sessions::uuid,
    local_dapp_sessions::address_id,
    local_dapp_sessions::dapp_id,
    local_dapp_sessions::last_used_at,
    local_dapp_sessions::created_at,
    local_dapp_sessions::updated_at,
);

const ALL_COLUMNS: AllColumns = (
    local_dapp_sessions::uuid,
    local_dapp_sessions::address_id,
    local_dapp_sessions::dapp_id,
    local_dapp_sessions::last_used_at,
    local_dapp_sessions::created_at,
    local_dapp_sessions::updated_at,
);

impl LocalDappSessionEntity {
    pub fn all_columns() -> AllColumns {
        ALL_COLUMNS
    }

    /// Fetch currently used chain id for a dapp session.
    pub fn fetch_eth_chain_id(
        &self,
        conn: &mut SqliteConnection,
    ) -> Result<eth::ChainId, Error> {
        use addresses::dsl as ad;
        use chains as c;
        use local_dapp_sessions::dsl as lds;

        let protocol_data_json: JsonValue = addresses::table
            .inner_join(
                local_dapp_sessions::table.on(lds::address_id.eq(ad::deterministic_id)),
            )
            .inner_join(chains::table.on(c::deterministic_id.eq(ad::chain_id)))
            .filter(lds::uuid.eq(&self.uuid))
            .select(c::protocol_data)
            .first::<JsonValue>(conn)?;
        let protocol_data: eth::ProtocolData = protocol_data_json.convert_into()?;

        Ok(protocol_data.chain_id)
    }

    pub fn fetch_account_id(&self, conn: &mut SqliteConnection) -> Result<String, Error> {
        m::Address::fetch_account_id(conn, &self.address_id)
    }

    pub fn fetch_address(&self, conn: &mut SqliteConnection) -> Result<String, Error> {
        m::Address::fetch_address(conn, &self.address_id)
    }
}

impl LocalDappSession {
    /// Fetch the current session for a dapp or create a new session.
    /// ⚠️ Assumes address exists already.
    pub fn create_eth_session_if_not_exists(
        tx_conn: &mut DeferredTxConnection,
        params: &DappSessionParams,
    ) -> Result<Self, Error> {
        if let Some(session) = Self::fetch_eth_session(tx_conn, params)? {
            Ok(session)
        } else {
            Self::create_eth_session(tx_conn, params)
        }
    }

    /// Create an Ethereum dapp session on default dapp chain for account and returns the sessions.
    /// ⚠️ Assumes address already exists and that there is one dapp key per account.
    pub fn create_eth_session(
        tx_conn: &mut DeferredTxConnection,
        params: &DappSessionParams,
    ) -> Result<Self, Error> {
        use accounts::dsl as ac;
        use addresses::dsl as ad;
        use asymmetric_keys::dsl as ak;
        use chains as c;
        use dapps::dsl as d;
        use local_dapp_sessions::dsl as lds;

        let protocol_data: JsonValue =
            JsonValue::convert_from(eth::ProtocolData::new(params.chain_id))?;

        // This assumes one dapp key per account.
        let address_id = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(ad::asymmetric_key_id)),
            )
            .inner_join(accounts::table.on(ac::deterministic_id.eq(ak::account_id)))
            .inner_join(dapps::table.on(d::deterministic_id.nullable().eq(ak::dapp_id)))
            .inner_join(chains::table.on(c::deterministic_id.eq(ad::chain_id)))
            .filter(ac::deterministic_id.eq(params.account_id))
            .filter(d::deterministic_id.eq(params.dapp_id))
            .filter(c::protocol_data.eq(&protocol_data))
            .select(ad::deterministic_id)
            .first::<String>(tx_conn.as_mut())?;

        let session_id = new_uuid();
        let created_at = rfc3339_timestamp();

        diesel::insert_into(local_dapp_sessions::table)
            .values((
                lds::uuid.eq(&session_id),
                lds::address_id.eq(&address_id),
                lds::dapp_id.eq(params.dapp_id),
                lds::last_used_at.eq(&created_at),
                lds::created_at.eq(&created_at),
                lds::updated_at.eq(&created_at),
            ))
            .execute(tx_conn.as_mut())?;

        // No `returning` support for insert in Diesel unfortunately.
        Self::fetch_session_by_id(tx_conn, &session_id)
    }

    /// Fetch dapp session.
    fn fetch_session_by_id(
        tx_conn: &mut DeferredTxConnection,
        session_id: &str,
    ) -> Result<Self, Error> {
        use local_dapp_sessions::dsl as lds;

        let entity: LocalDappSessionEntity = local_dapp_sessions::table
            .filter(lds::uuid.eq(session_id))
            .select(LocalDappSessionEntity::all_columns())
            .first(tx_conn.as_mut())?;

        Self::from_entity(tx_conn, entity)
    }

    /// Fetch dapp session.
    pub fn fetch_eth_session(
        tx_conn: &mut DeferredTxConnection,
        params: &DappSessionParams,
    ) -> Result<Option<Self>, Error> {
        use accounts::dsl as ac;
        use addresses::dsl as ad;
        use asymmetric_keys::dsl as ak;
        use local_dapp_sessions::dsl as lds;

        let entity: Option<LocalDappSessionEntity> = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(ad::asymmetric_key_id)),
            )
            .inner_join(accounts::table.on(ac::deterministic_id.eq(ak::account_id)))
            .inner_join(
                local_dapp_sessions::table.on(lds::address_id.eq(ad::deterministic_id)),
            )
            .filter(ac::deterministic_id.eq(params.account_id))
            .filter(lds::dapp_id.eq(params.dapp_id))
            .select(LocalDappSessionEntity::all_columns())
            .first(tx_conn.as_mut())
            .optional()?;

        let session = match entity {
            Some(entity) => Some(Self::from_entity(tx_conn, entity)?),
            None => None,
        };
        Ok(session)
    }

    fn from_entity(
        tx_conn: &mut DeferredTxConnection,
        entity: LocalDappSessionEntity,
    ) -> Result<Self, Error> {
        let chain_id = entity.fetch_eth_chain_id(tx_conn.as_mut())?;
        let account_id = entity.fetch_account_id(tx_conn.as_mut())?;
        let address = entity.fetch_address(tx_conn.as_mut())?;

        let LocalDappSessionEntity {
            uuid,
            address_id,
            dapp_id,
            ..
        } = entity;
        let session = LocalDappSession::builder()
            .uuid(uuid)
            .address_id(address_id)
            .dapp_id(dapp_id)
            .chain_id(chain_id)
            .account_id(account_id)
            .address(address)
            .build();
        Ok(session)
    }

    /// Update currently used address for a dapp session.
    pub fn update_session_address(
        self,
        tx_conn: &mut DeferredTxConnection,
        new_address_id: &str,
    ) -> Result<Self, Error> {
        use local_dapp_sessions::dsl as lds;

        // There is a unique constraint on address
        diesel::update(local_dapp_sessions::table.filter(lds::uuid.eq(&self.uuid)))
            .set((
                lds::address_id.eq(new_address_id),
                lds::updated_at.eq(rfc3339_timestamp()),
            ))
            .execute(tx_conn.as_mut())?;

        Self::fetch_session_by_id(tx_conn, &self.uuid)
    }

    pub fn update_last_used_at(
        self,
        tx_conn: &mut DeferredTxConnection,
    ) -> Result<Self, Error> {
        use local_dapp_sessions::dsl as lds;

        diesel::update(local_dapp_sessions::table.filter(lds::uuid.eq(&self.uuid)))
            .set(lds::last_used_at.eq(rfc3339_timestamp()))
            .execute(tx_conn.as_mut())?;

        Self::fetch_session_by_id(tx_conn, &self.uuid)
    }
}
