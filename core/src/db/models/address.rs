// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashSet, str::FromStr};

use derive_more::{AsRef, Display, Into};
use diesel::{
    deserialize::FromSql,
    expression::AsExpression,
    prelude::*,
    serialize::ToSql,
    sql_types::{Bool, Text},
    sqlite::Sqlite,
    SqliteConnection,
};
use generic_array::{typenum::U2, GenericArray};
use typed_builder::TypedBuilder;

use crate::{
    db::{
        deterministic_id::{DeriveDeterministicId, DeterministicId, EntityName},
        models as m,
        models::{DataEncryptionKey, NewAsymmetricKey},
        schema::{
            addresses, asymmetric_keys, chains, dapps, data_encryption_keys, profiles,
        },
        DeferredTxConnection, JsonValue,
    },
    encryption::{KeyEncryptionKey, KeyName, Keychain},
    protocols::{eth, BlockchainProtocol},
    utils::rfc3339_timestamp,
    Error,
};

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
#[diesel(table_name = addresses)]
pub struct Address {
    pub deterministic_id: AddressId,
    pub asymmetric_key_id: DeterministicId,
    pub chain_id: DeterministicId,
    pub address: eth::ChecksumAddress,
    pub created_at: String,
    pub updated_at: Option<String>,
}

type AllColumns = (
    addresses::deterministic_id,
    addresses::asymmetric_key_id,
    addresses::chain_id,
    addresses::address,
    addresses::created_at,
    addresses::updated_at,
);

const ALL_COLUMNS: AllColumns = (
    addresses::deterministic_id,
    addresses::asymmetric_key_id,
    addresses::chain_id,
    addresses::address,
    addresses::created_at,
    addresses::updated_at,
);

impl Address {
    pub fn all_columns() -> AllColumns {
        ALL_COLUMNS
    }

    pub fn list_all(conn: &mut SqliteConnection) -> Result<Vec<Self>, Error> {
        Ok(addresses::table.load::<Self>(conn)?)
    }

    /// Returns the wallet addresses of an profile.
    pub fn list_profile_wallets(
        conn: &mut SqliteConnection,
        profile_id: &DeterministicId,
    ) -> Result<Vec<Self>, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let wallets: Vec<Self> = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(ak::profile_id.eq(profile_id))
            .filter(ak::is_profile_wallet.eq(true))
            .select(Self::all_columns())
            .load(conn)?;

        Ok(wallets)
    }

    /// Returns the addresses for a dapp in an profile.
    pub fn list_for_dapp(
        conn: &mut SqliteConnection,
        params: &ListAddressesForDappParams,
    ) -> Result<Vec<Self>, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;
        use dapps::dsl as d;

        let addresses: Vec<Self> = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .inner_join(dapps::table.on(ak::dapp_id.eq(d::deterministic_id.nullable())))
            .filter(d::deterministic_id.eq(params.dapp_id))
            .filter(ak::profile_id.eq(params.profile_id))
            .select(Self::all_columns())
            .load(conn)?;

        Ok(addresses)
    }

    /// Add an Ethereum chain for an address.
    /// The operation is idempotent.
    /// Returns the address DB id of the address on the chain.
    pub fn fetch_or_create_for_eth_chain(
        tx_conn: &mut DeferredTxConnection,
        address_id: &AddressId,
        chain_id: eth::ChainId,
    ) -> Result<AddressId, Error> {
        let chain_entity_id = m::Chain::fetch_or_create_eth_chain_id(tx_conn, chain_id)?;
        let asymmetric_key_id = Self::fetch_key_id(tx_conn.as_mut(), address_id)?;
        let address_entity = AddressEntity::builder()
            .asymmetric_key_id(&asymmetric_key_id)
            .chain_entity_id(&chain_entity_id)
            .build();
        let added_address_id =
            Self::fetch_or_create_for_eth_chain_with_entity(tx_conn, &address_entity)?;
        Ok(added_address_id)
    }

    /// Create an Ethereum signing key and derived address.
    /// Returns the address id.
    pub fn create_eth_key_and_address(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        params: &CreateEthAddressParams,
    ) -> Result<AddressId, Error> {
        let sk_kek = KeyEncryptionKey::sk_kek(keychain)?;
        let (dek_id, sk_dek) = DataEncryptionKey::fetch_dek(
            tx_conn.as_mut(),
            KeyName::SkDataEncryptionKey,
            &sk_kek,
        )?;

        let signing_key = eth::EthereumAsymmetricKey::random()?;
        let encrypted_signing_key = signing_key.to_encrypted_der(&sk_dek)?;
        let public_key = signing_key.public_key_der()?;

        let key_id = NewAsymmetricKey::builder()
            .profile_id(params.profile_id)
            .dek_id(&dek_id)
            .elliptic_curve(signing_key.curve)
            .public_key(public_key.as_slice())
            .encrypted_der(&encrypted_signing_key)
            .dapp_id(params.dapp_id)
            .is_profile_wallet(params.is_profile_wallet)
            .build()
            .insert(tx_conn)?;

        let checksum_address = eth::ChecksumAddress::new(&signing_key.public_key)?;
        let address_id = NewAddress::builder()
            .asymmetric_key_id(&key_id)
            .address(&checksum_address)
            .build()
            .insert_eth(tx_conn, params.chain_id)?;

        Ok(address_id)
    }

    /// Fetch or create an address id for an Ethereum chain for an existing key.
    pub fn fetch_or_create_for_eth_chain_with_entity(
        tx_conn: &mut DeferredTxConnection,
        address_entity: &AddressEntity,
    ) -> Result<AddressId, Error> {
        match Self::exists(tx_conn.as_mut(), address_entity)? {
            Some(deterministic_id) => Ok(deterministic_id),
            None => {
                let public_key = m::AsymmetricKey::fetch_eth_public_key(
                    tx_conn.as_mut(),
                    address_entity.asymmetric_key_id,
                )?;
                let checksum_address = eth::ChecksumAddress::new(&public_key)?;
                NewAddress::builder()
                    .asymmetric_key_id(address_entity.asymmetric_key_id)
                    .address(&checksum_address)
                    .build()
                    .insert_eth_for_chain_entity(tx_conn, address_entity.chain_entity_id)
            }
        }
    }

    fn exists(
        conn: &mut SqliteConnection,
        address_entity: &AddressEntity,
    ) -> Result<Option<AddressId>, Error> {
        use addresses::dsl as a;

        let address_id = address_entity.address_id()?;

        let exists: Option<bool> = addresses::table
            .filter(a::deterministic_id.eq(&address_id))
            .select(AsExpression::<Bool>::as_expression(true))
            .first(conn)
            .optional()?;

        Ok(exists.map(|_| address_id))
    }

    /// Fetch the the address entity by id.
    pub fn fetch(
        conn: &mut SqliteConnection,
        address_id: &AddressId,
    ) -> Result<Self, Error> {
        use addresses::dsl as a;

        let address: Self = addresses::table
            .filter(a::deterministic_id.eq(address_id))
            .select(ALL_COLUMNS)
            .first(conn)?;

        Ok(address)
    }

    pub fn fetch_profile_id(
        conn: &mut SqliteConnection,
        address_id: &AddressId,
    ) -> Result<DeterministicId, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let profile_id = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(a::deterministic_id.eq(address_id))
            .select(ak::profile_id)
            .first(conn)?;

        Ok(profile_id)
    }

    pub fn fetch_profile_name(
        conn: &mut SqliteConnection,
        address_id: &AddressId,
    ) -> Result<String, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;
        use profiles::dsl as p;

        let profile_name = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .inner_join(profiles::table.on(ak::profile_id.eq(p::deterministic_id)))
            .filter(a::deterministic_id.eq(address_id))
            .select(p::name)
            .first(conn)?;

        Ok(profile_name)
    }

    pub fn is_profile_wallet(
        conn: &mut SqliteConnection,
        address_id: &AddressId,
    ) -> Result<bool, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let is_profile_wallet = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(a::deterministic_id.eq(address_id))
            .select(ak::is_profile_wallet)
            .first(conn)?;

        Ok(is_profile_wallet)
    }

    /// If this is a dapp key, return its human identifier.
    pub fn dapp_identifier(
        conn: &mut SqliteConnection,
        address_id: &AddressId,
    ) -> Result<Option<String>, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;
        use dapps::dsl as d;

        let human_identifier = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .inner_join(dapps::table.on(ak::dapp_id.eq(d::deterministic_id.nullable())))
            .filter(a::deterministic_id.eq(address_id))
            .select(d::identifier)
            .first(conn)
            .optional()?;

        Ok(human_identifier)
    }

    /// Fet the asymmetric key's DB id for an address.
    pub fn fetch_key_id(
        conn: &mut SqliteConnection,
        address_id: &AddressId,
    ) -> Result<DeterministicId, Error> {
        use addresses::dsl as a;

        let asymmetric_key_id = addresses::table
            .filter(a::deterministic_id.eq(address_id))
            .select(a::asymmetric_key_id)
            .first(conn)?;

        Ok(asymmetric_key_id)
    }

    /// Fetch the blockchain address.
    pub fn fetch_address(
        conn: &mut SqliteConnection,
        address_id: &AddressId,
    ) -> Result<eth::ChecksumAddress, Error> {
        use addresses::dsl as a;

        let address = addresses::table
            .filter(a::deterministic_id.eq(address_id))
            .select(a::address)
            .first(conn)?;

        Ok(address)
    }

    pub fn fetch_eth_chains_for_address(
        conn: &mut SqliteConnection,
        address: eth::ChecksumAddress,
    ) -> Result<Vec<eth::ChainId>, Error> {
        use addresses::dsl as a;
        use chains::dsl as c;

        let protocol_data: Vec<JsonValue> = addresses::table
            .inner_join(chains::table.on(a::chain_id.eq(c::deterministic_id)))
            .filter(a::address.eq(address))
            .select(c::protocol_data)
            .load(conn)?;

        let mut results: Vec<eth::ChainId> = Default::default();
        for pd in protocol_data.into_iter() {
            let chain_data: eth::ProtocolData = pd.convert_into()?;
            results.push(chain_data.chain_id);
        }

        Ok(results)
    }

    /// Fetch all address ids for an Ethereum checksum addresses.
    fn fetch_by_eth_address(
        conn: &mut SqliteConnection,
        address: eth::ChecksumAddress,
    ) -> Result<Vec<AddressId>, Error> {
        use addresses::dsl as a;

        let (address_ids, key_ids): (Vec<AddressId>, Vec<String>) = addresses::table
            .filter(a::address.eq(address))
            .select((a::deterministic_id, a::asymmetric_key_id))
            .load(conn)?
            .into_iter()
            .unzip();

        // Sanity check to make sure we don't have multiple keys with the same checksum address.
        // There is no unique index on (address, chain_id) due to deterministic id constraints.
        let unique_keys = key_ids.iter().collect::<HashSet<_>>();
        if unique_keys.len() > 1 {
            return Err(Error::Fatal {
                error: "Multiple keys with the same checksum address".to_string(),
            });
        }

        Ok(address_ids)
    }

    /// Fetch all chain ids for a checksum address.
    pub fn fetch_chains_for_address(
        conn: &mut DeferredTxConnection,
        address: eth::ChecksumAddress,
    ) -> Result<Vec<eth::ChainId>, Error> {
        let addresses = Self::fetch_by_eth_address(conn.as_mut(), address)?;
        addresses
            .iter()
            .map(|address_id| Self::fetch_eth_chain_id(conn.as_mut(), address_id))
            .collect()
    }

    /// Fetch the address id by the checksum address on a given chain if the checksum address is in
    /// the DB.
    pub fn fetch_or_create_id_by_address_on_chain(
        tx_conn: &mut DeferredTxConnection,
        address: eth::ChecksumAddress,
        chain_id: eth::ChainId,
    ) -> Result<Option<AddressId>, Error> {
        let address_ids = Self::fetch_by_eth_address(tx_conn.as_mut(), address)?;
        address_ids
            .into_iter()
            .next()
            .map(|same_address_id| {
                // No-op if the chain exists, just returns the address id.
                Self::fetch_or_create_for_eth_chain(tx_conn, &same_address_id, chain_id)
            })
            .transpose()
    }

    /// Fetch the wallet address id for an Ethereum chain in an profile.
    /// Assumes one wallet address per profile per chain.
    pub fn fetch_eth_wallet_id(
        tx_conn: &mut DeferredTxConnection,
        profile_id: &DeterministicId,
        eth_chain_id: eth::ChainId,
    ) -> Result<AddressId, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let chain_id = m::Chain::fetch_or_create_eth_chain_id(tx_conn, eth_chain_id)?;

        let address_id = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(a::chain_id.eq(&chain_id))
            .filter(ak::profile_id.eq(profile_id))
            .filter(ak::is_profile_wallet.eq(true))
            .select(a::deterministic_id)
            .first(tx_conn.as_mut())?;

        Ok(address_id)
    }

    pub fn fetch_profile_id_for_eth_address(
        connection: &mut SqliteConnection,
        checksum_address: eth::ChecksumAddress,
    ) -> Result<Option<DeterministicId>, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let profile_id = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(a::address.eq(checksum_address))
            .select(ak::profile_id)
            .first(connection)
            .optional()?;

        Ok(profile_id)
    }

    pub fn fetch_eth_signing_key(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        address_id: &AddressId,
    ) -> Result<eth::SigningKey, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;
        use chains::dsl as c;
        use data_encryption_keys::dsl as dek;

        use crate::encryption::EncryptionOutput;

        let (dek_name, encrypted_der, protocol_data) = asymmetric_keys::table
            .inner_join(
                addresses::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .inner_join(
                data_encryption_keys::table.on(ak::dek_id.eq(dek::deterministic_id)),
            )
            .inner_join(chains::table.on(a::chain_id.eq(c::deterministic_id)))
            .filter(a::deterministic_id.eq(address_id))
            .filter(c::protocol.eq(BlockchainProtocol::Ethereum))
            .select((dek::name, ak::encrypted_der, c::protocol_data))
            .first::<(String, EncryptionOutput, JsonValue)>(tx_conn.as_mut())?;

        let protocol_data: eth::ProtocolData = protocol_data.convert_into()?;
        let dek_name = KeyName::from_str(&dek_name).map_err(|_| Error::Fatal {
            error: format!("Unknown DEK name: {dek_name}"),
        })?;

        let sk_kek = KeyEncryptionKey::sk_kek(keychain)?;
        let (_, sk_dek) =
            DataEncryptionKey::fetch_dek(tx_conn.as_mut(), dek_name, &sk_kek)?;
        let key =
            eth::EthereumAsymmetricKey::from_encrypted_der(&encrypted_der, &sk_dek)?;
        let signing_key = eth::SigningKey::new(key, protocol_data.chain_id)?;

        Ok(signing_key)
    }

    pub fn fetch_eth_chain_id(
        conn: &mut SqliteConnection,
        address_id: &AddressId,
    ) -> Result<eth::ChainId, Error> {
        use addresses::dsl as a;
        use chains::dsl as c;

        let protocol_data = addresses::table
            .inner_join(chains::table.on(a::chain_id.eq(c::deterministic_id)))
            .filter(a::deterministic_id.eq(address_id))
            .filter(c::protocol.eq(BlockchainProtocol::Ethereum))
            .select(c::protocol_data)
            .first::<JsonValue>(conn)?;

        let protocol_data: eth::ProtocolData = protocol_data.convert_into()?;
        Ok(protocol_data.chain_id)
    }
}

#[derive(TypedBuilder, Insertable)]
#[diesel(table_name = addresses)]
#[readonly::make]
struct NewAddress<'a> {
    #[builder(setter(into))]
    pub asymmetric_key_id: &'a DeterministicId,
    #[builder(setter(into))]
    pub address: &'a eth::ChecksumAddress,
}

impl<'a> NewAddress<'a> {
    /// Create a new asymmetric key and return its deterministic id.
    pub fn insert_eth(
        &self,
        tx_conn: &mut DeferredTxConnection,
        eth_chain_id: eth::ChainId,
    ) -> Result<AddressId, Error> {
        let chain_entity_id =
            m::Chain::fetch_or_create_eth_chain_id(tx_conn, eth_chain_id)?;
        self.insert_eth_for_chain_entity(tx_conn, &chain_entity_id)
    }

    pub fn insert_eth_for_chain_entity(
        &self,
        tx_conn: &mut DeferredTxConnection,
        chain_entity_id: &DeterministicId,
    ) -> Result<AddressId, Error> {
        use addresses::dsl as a;

        let entity = AddressEntity {
            asymmetric_key_id: self.asymmetric_key_id,
            chain_entity_id,
        };
        let deterministic_id = entity.address_id()?;
        let created_at = rfc3339_timestamp();

        diesel::insert_into(addresses::table)
            .values((
                self,
                a::chain_id.eq(&chain_entity_id),
                a::deterministic_id.eq(&deterministic_id),
                a::created_at.eq(&created_at),
            ))
            .execute(tx_conn.as_mut())?;

        Ok(deterministic_id)
    }
}

#[derive(Clone, Debug, TypedBuilder)]
#[readonly::make]
pub struct AddressEntity<'a> {
    pub asymmetric_key_id: &'a DeterministicId,
    pub chain_entity_id: &'a DeterministicId,
}

impl AddressEntity<'_> {
    // TODO move this to DeterministicId trait
    fn address_id(&self) -> Result<AddressId, Error> {
        Ok(self.deterministic_id()?.into())
    }
}

impl<'a> DeriveDeterministicId<'a, &'a str, U2> for AddressEntity<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::Address
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U2> {
        [
            self.asymmetric_key_id.as_ref(),
            self.chain_entity_id.as_ref(),
        ]
        .into()
    }
}

#[derive(Clone, Debug, TypedBuilder)]
#[readonly::make]
pub struct ListAddressesForDappParams<'a> {
    pub profile_id: &'a DeterministicId,
    pub dapp_id: &'a DeterministicId,
}

#[derive(Clone, Debug, TypedBuilder)]
#[readonly::make]
pub struct CreateEthAddressParams<'a> {
    pub profile_id: &'a DeterministicId,
    #[builder(setter(into))]
    pub chain_id: eth::ChainId,
    #[builder(default = None)]
    pub dapp_id: Option<&'a DeterministicId>,
    #[builder(default = false)]
    pub is_profile_wallet: bool,
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
pub struct AddressId(String);

impl From<DeterministicId> for AddressId {
    fn from(value: DeterministicId) -> Self {
        Self(value.into())
    }
}

impl TryFrom<String> for AddressId {
    type Error = Error;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        Ok(DeterministicId::try_from(s)?.into())
    }
}

impl FromStr for AddressId {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.to_string().try_into()
    }
}

// TODO derive macro
impl FromSql<Text, Sqlite> for AddressId {
    fn from_sql(
        bytes: diesel::backend::RawValue<Sqlite>,
    ) -> diesel::deserialize::Result<Self> {
        let s = <String as FromSql<Text, Sqlite>>::from_sql(bytes)?;
        let address_id: AddressId = s.parse()?;
        Ok(address_id)
    }
}

impl ToSql<Text, Sqlite> for AddressId {
    fn to_sql(
        &self,
        out: &mut diesel::serialize::Output<Sqlite>,
    ) -> diesel::serialize::Result {
        let s = self.to_string();
        out.set_value(s);
        Ok(diesel::serialize::IsNull::No)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;
    use crate::app_core::tests::TmpCore;

    #[test]
    fn profile_id_fk_is_enforced() -> Result<()> {
        let tmp_core = TmpCore::new()?;

        let profile_id: DeterministicId =
            "B7UREO2PJCCWSSZRBQEUO64A5DS2XRVO6RLOF5XYVAVT7T6KPYNQ".parse()?;
        let params = CreateEthAddressParams::builder()
            .profile_id(&profile_id)
            .chain_id(eth::ChainId::EthMainnet)
            .is_profile_wallet(true)
            .build();

        let res = tmp_core
            .connection_pool()
            .deferred_transaction(|mut tx_conn| {
                Address::create_eth_key_and_address(
                    &mut tx_conn,
                    tmp_core.keychain(),
                    &params,
                )
            });

        assert!(res.is_err());
        assert!(res
            .err()
            .unwrap()
            .to_string()
            .to_lowercase()
            .contains("foreignkey"));

        Ok(())
    }
}
