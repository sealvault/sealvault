// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::prelude::*;
use typed_builder::TypedBuilder;

use crate::{
    db::{
        models as m,
        models::AddressId,
        schema::{addresses, asymmetric_keys, chains, local_dapp_sessions, profiles},
        DeferredTxConnection, DeterministicId, JsonValue,
    },
    protocols::eth,
    utils::{new_uuid, rfc3339_timestamp},
    Error,
};

/// Not synced because it holds data that may differ between devices simultaneously.
/// Eg. a user might want to use a dapp on Ethereum on desktop and on Polygon on mobile.
#[derive(Clone, Debug, PartialEq, Eq, TypedBuilder)]
pub struct LocalDappSession {
    pub uuid: String,

    pub profile_id: DeterministicId,

    pub address_id: AddressId,
    pub address: eth::ChecksumAddress,

    pub dapp_id: DeterministicId,
    pub dapp_human_identifier: String,

    pub chain_id: eth::ChainId,
}

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(uuid))]
#[diesel(table_name = local_dapp_sessions)]
#[readonly::make]
struct LocalDappSessionEntity {
    uuid: String,
    address_id: AddressId,
    dapp_id: DeterministicId,
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

    pub fn fetch_profile_id(
        &self,
        conn: &mut SqliteConnection,
    ) -> Result<DeterministicId, Error> {
        m::Address::fetch_profile_id(conn, &self.address_id)
    }

    pub fn fetch_address(
        &self,
        conn: &mut SqliteConnection,
    ) -> Result<eth::ChecksumAddress, Error> {
        m::Address::fetch_address(conn, &self.address_id)
    }

    pub fn fetch_dapp_identifier(
        &self,
        conn: &mut SqliteConnection,
    ) -> Result<String, Error> {
        m::Dapp::fetch_dapp_identifier(conn, &self.dapp_id)
    }
}

impl LocalDappSession {
    /// List dapp ids in descending order by last used.
    pub fn list_dapp_ids_desc(
        conn: &mut SqliteConnection,
        limit: u32,
    ) -> Result<Vec<DeterministicId>, Error> {
        use local_dapp_sessions::dsl as lds;

        let dapp_ids: Vec<DeterministicId> = local_dapp_sessions::table
            .select(lds::dapp_id)
            .order(lds::last_used_at.desc())
            .limit(limit as i64)
            .load(conn)?;

        Ok(dapp_ids)
    }

    /// Fetch the current session for a dapp or create a new session.
    /// ⚠️ Assumes key for dapp in profile already exists already and that there is one dapp key
    /// per profile.
    pub fn create_eth_session_if_not_exists(
        tx_conn: &mut DeferredTxConnection,
        params: &NewDappSessionParams,
    ) -> Result<Self, Error> {
        if let Some(session) = Self::fetch_eth_session(tx_conn, params)? {
            Ok(session)
        } else {
            Self::create_eth_session(tx_conn, params)
        }
    }

    /// Create an Ethereum dapp session on default dapp chain for profile and returns the sessions.
    /// ⚠️ Assumes key for dapp in profile already exists already and that there is one dapp key
    /// per profile.
    pub fn create_eth_session<'a>(
        tx_conn: &mut DeferredTxConnection,
        params: &'a impl DappSessionParamsWithChain<'a>,
    ) -> Result<Self, Error> {
        use local_dapp_sessions::dsl as lds;

        // This assumes one dapp key per profile.
        let chain_entity_id =
            m::Chain::fetch_or_create_eth_chain_id(tx_conn, params.chain_id())?;
        let asymmetric_key_id =
            m::AsymmetricKey::fetch_id_for_dapp(tx_conn.as_mut(), params)?;
        let address_entity = m::AddressEntity::builder()
            .asymmetric_key_id(&asymmetric_key_id)
            .chain_entity_id(&chain_entity_id)
            .build();

        let address_id =
            m::Address::fetch_or_create_for_eth_chain(tx_conn, &address_entity)?;

        let session_id = new_uuid();
        let created_at = rfc3339_timestamp();

        diesel::insert_into(local_dapp_sessions::table)
            .values((
                lds::uuid.eq(&session_id),
                lds::address_id.eq(&address_id),
                lds::dapp_id.eq(params.dapp_id()),
                lds::last_used_at.eq(&created_at),
                lds::created_at.eq(&created_at),
                lds::updated_at.eq(&created_at),
            ))
            .execute(tx_conn.as_mut())?;

        // No `returning` support for Sqlite insert in Diesel unfortunately.
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
    pub fn fetch_eth_session<'a>(
        tx_conn: &mut DeferredTxConnection,
        params: &'a impl DappSessionParams<'a>,
    ) -> Result<Option<Self>, Error> {
        use addresses::dsl as ad;
        use asymmetric_keys::dsl as ak;
        use local_dapp_sessions::dsl as lds;
        use profiles::dsl as p;

        let entity: Option<LocalDappSessionEntity> = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(ad::asymmetric_key_id)),
            )
            .inner_join(profiles::table.on(p::deterministic_id.eq(ak::profile_id)))
            .inner_join(
                local_dapp_sessions::table.on(lds::address_id.eq(ad::deterministic_id)),
            )
            .filter(p::deterministic_id.eq(params.profile_id()))
            .filter(lds::dapp_id.eq(params.dapp_id()))
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
        let profile_id = entity.fetch_profile_id(tx_conn.as_mut())?;
        let address = entity.fetch_address(tx_conn.as_mut())?;
        let dapp_human_identifier = entity.fetch_dapp_identifier(tx_conn.as_mut())?;

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
            .dapp_human_identifier(dapp_human_identifier)
            .chain_id(chain_id)
            .profile_id(profile_id)
            .address(address)
            .build();
        Ok(session)
    }

    /// Update currently used address for a dapp session.
    fn update_session_address(
        self,
        tx_conn: &mut DeferredTxConnection,
        new_address_id: &AddressId,
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

    /// Assumes there is a key already for the dapp in the profile.
    pub fn change_eth_chain(
        self,
        tx_conn: &mut DeferredTxConnection,
        new_chain_id: eth::ChainId,
    ) -> Result<Self, Error> {
        let chain_entity_id =
            m::Chain::fetch_or_create_eth_chain_id(tx_conn, new_chain_id)?;

        let asymmetric_key_id =
            m::Address::fetch_key_id(tx_conn.as_mut(), &self.address_id)?;
        let address_entity = m::AddressEntity::builder()
            .asymmetric_key_id(&asymmetric_key_id)
            .chain_entity_id(&chain_entity_id)
            .build();
        let new_address_id =
            m::Address::fetch_or_create_for_eth_chain(tx_conn, &address_entity)?;

        self.update_session_address(tx_conn, &new_address_id)
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

#[derive(Debug, Clone, TypedBuilder)]
#[readonly::make]
pub struct NewDappSessionParams<'a> {
    pub dapp_id: &'a DeterministicId,
    pub profile_id: &'a DeterministicId,
    #[builder(default = eth::ChainId::default_dapp_chain())]
    pub chain_id: eth::ChainId,
}

#[derive(Debug, Clone, TypedBuilder)]
#[readonly::make]
pub struct FetchDappSessionParams<'a> {
    pub dapp_id: &'a DeterministicId,
    pub profile_id: &'a DeterministicId,
}

pub trait DappSessionParams<'a> {
    fn dapp_id(&'a self) -> &'a DeterministicId;
    fn profile_id(&'a self) -> &'a DeterministicId;
}

pub trait DappSessionParamsWithChain<'a>: DappSessionParams<'a> {
    fn chain_id(&'a self) -> eth::ChainId;
}

impl<'a> DappSessionParams<'a> for NewDappSessionParams<'a> {
    fn dapp_id(&'a self) -> &'a DeterministicId {
        self.dapp_id
    }

    fn profile_id(&'a self) -> &'a DeterministicId {
        self.profile_id
    }
}

impl<'a> DappSessionParamsWithChain<'a> for NewDappSessionParams<'a> {
    fn chain_id(&'a self) -> eth::ChainId {
        self.chain_id
    }
}

impl<'a> DappSessionParams<'a> for FetchDappSessionParams<'a> {
    fn dapp_id(&'a self) -> &'a DeterministicId {
        self.dapp_id
    }

    fn profile_id(&'a self) -> &'a DeterministicId {
        self.profile_id
    }
}
