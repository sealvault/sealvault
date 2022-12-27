// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::{prelude::*, SqliteConnection};
use generic_array::{typenum::U2, GenericArray};

use crate::{
    db::{
        deterministic_id::{DeterministicId, EntityName},
        schema::chains,
        DeferredTxConnection, JsonValue,
    },
    protocols::{eth, BlockchainProtocol},
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
#[diesel(table_name = chains)]
pub struct Chain {
    pub deterministic_id: String,
    pub protocol: BlockchainProtocol,
    pub protocol_data: JsonValue,
    pub user_settings: JsonValue,
    pub created_at: String,
    pub updated_at: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EthChain {
    pub db_id: String,
    pub chain_id: eth::ChainId,
    pub user_settings: eth::ChainSettings,
}

impl TryFrom<Chain> for EthChain {
    type Error = Error;

    fn try_from(chain: Chain) -> Result<Self, Self::Error> {
        let Chain {
            deterministic_id,
            protocol,
            protocol_data,
            user_settings,
            ..
        } = chain;
        if protocol != BlockchainProtocol::Ethereum {
            return Err(Error::Fatal {
                error: format!("Expected Ethereum protocol, instead got: {}", protocol),
            });
        }
        let chain_data: eth::ProtocolData = protocol_data.convert_into()?;
        let user_settings: eth::ChainSettings = user_settings.convert_into()?;

        Ok(Self {
            db_id: deterministic_id,
            chain_id: chain_data.chain_id,
            user_settings,
        })
    }
}

impl Chain {
    pub fn list_eth_chains(conn: &mut SqliteConnection) -> Result<Vec<EthChain>, Error> {
        use chains::dsl as c;

        let chains: Vec<Chain> = chains::table
            .filter(c::protocol.eq(BlockchainProtocol::Ethereum))
            .load::<Self>(conn)?;

        let mut results: Vec<EthChain> = Default::default();
        for chain in chains {
            results.push(chain.try_into()?)
        }

        Ok(results)
    }

    /// Fetch an Ethereum chain id by the db entity's deterministic id.
    pub fn fetch_eth_chain_id(
        conn: &mut SqliteConnection,
        deterministic_id: &str,
    ) -> Result<eth::ChainId, Error> {
        use chains::dsl as c;
        let protocol_data: JsonValue = chains::table
            .filter(c::deterministic_id.eq(&deterministic_id))
            .select(c::protocol_data)
            .first(conn)?;

        let protocol_data: eth::ProtocolData = protocol_data.convert_into()?;

        Ok(protocol_data.chain_id)
    }

    /// Fetch the deterministic id for an Ethereum chain.
    /// Creates the chain entity if it's not in the db yet.
    /// Returns the chain's DB id.
    pub fn fetch_or_create_eth_chain_id(
        conn: &mut DeferredTxConnection,
        chain_id: eth::ChainId,
    ) -> Result<String, Error> {
        match Self::fetch_eth_chain_deterministic_id(conn.as_mut(), chain_id)? {
            Some(chain_id) => Ok(chain_id),
            None => Self::create_eth_chain(conn.as_mut(), chain_id),
        }
    }

    pub fn fetch_user_settings_for_eth_chain(
        conn: &mut SqliteConnection,
        chain_id: eth::ChainId,
    ) -> Result<eth::ChainSettings, Error> {
        use chains::dsl as c;

        let chain_entity = ChainEntity::new_eth(chain_id)?;
        let deterministic_id = chain_entity.deterministic_id()?;

        let settings: JsonValue = chains::table
            .filter(c::deterministic_id.eq(&*deterministic_id))
            .select(c::user_settings)
            .first(conn)?;
        settings.convert_into()
    }

    /// Fetch an Ethereum chain and return its deterministic id if it exists.
    fn fetch_eth_chain_deterministic_id(
        conn: &mut SqliteConnection,
        chain_id: eth::ChainId,
    ) -> Result<Option<String>, Error> {
        use chains::dsl as c;

        let protocol_data = JsonValue::convert_from(eth::ProtocolData::new(chain_id))?;

        let deterministic_id = chains::table
            .filter(c::protocol.eq(BlockchainProtocol::Ethereum))
            .filter(c::protocol_data.eq(&protocol_data))
            .select(c::deterministic_id)
            .first(conn)
            .optional()?;

        Ok(deterministic_id)
    }

    /// Create an Ethereum chain and return its deterministic id.
    fn create_eth_chain(
        conn: &mut SqliteConnection,
        chain_id: eth::ChainId,
    ) -> Result<String, Error> {
        use chains::dsl as c;

        let protocol_data = JsonValue::convert_from(eth::ProtocolData::new(chain_id))?;
        let user_settings = JsonValue::convert_from(chain_id.default_user_settings())?;

        let chain_entity = ChainEntity::new_eth(chain_id)?;
        let deterministic_id = chain_entity.deterministic_id()?;

        let created_at = rfc3339_timestamp();

        diesel::insert_into(chains::table)
            .values((
                c::deterministic_id.eq(&deterministic_id),
                c::protocol.eq(BlockchainProtocol::Ethereum),
                c::protocol_data.eq(&protocol_data),
                c::user_settings.eq(&user_settings),
                c::created_at.eq(&created_at),
            ))
            .execute(conn)?;

        Ok(deterministic_id)
    }
}

#[readonly::make]
struct ChainEntity {
    pub protocol: String,
    pub protocol_data: String,
}

impl ChainEntity {
    fn new_eth(chain_id: eth::ChainId) -> Result<Self, Error> {
        let protocol_data = JsonValue::convert_from(eth::ProtocolData::new(chain_id))?;
        Ok(Self {
            protocol: BlockchainProtocol::Ethereum.to_string(),
            protocol_data: protocol_data.canonical_json()?,
        })
    }
}

impl<'a> DeterministicId<'a, &'a str, U2> for ChainEntity {
    fn entity_name(&'a self) -> EntityName {
        EntityName::Chain
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U2> {
        [&*self.protocol, &*self.protocol_data].into()
    }
}
