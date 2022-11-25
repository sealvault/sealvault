// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
use std::str::FromStr;

use diesel::{expression::AsExpression, prelude::*, sql_types::Bool, SqliteConnection};
use generic_array::{typenum::U2, GenericArray};
use typed_builder::TypedBuilder;

use crate::{
    db::{
        deterministic_id::{DeterministicId, EntityName},
        models as m,
        models::{DataEncryptionKey, NewAsymmetricKey},
        schema::{
            accounts, addresses, asymmetric_keys, chains, dapps, data_encryption_keys,
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
    pub deterministic_id: String,
    pub asymmetric_key_id: String,
    pub chain_id: String,
    pub address: String,
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

    /// Returns the wallet addresses of an account.
    pub fn list_account_wallets(
        conn: &mut SqliteConnection,
        account_id: &str,
    ) -> Result<Vec<Self>, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let wallets: Vec<Self> = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(ak::account_id.eq(account_id))
            .filter(ak::is_account_wallet.eq(true))
            .select(Self::all_columns())
            .load(conn)?;

        Ok(wallets)
    }

    /// Returns the addresses for a dapp in an account.
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
            .filter(ak::account_id.eq(params.account_id))
            .select(Self::all_columns())
            .load(conn)?;

        Ok(addresses)
    }

    /// Add an Ethereum chain for an address.
    /// The operation is idempotent.
    /// Returns the address DB id of the address on the chain.
    pub fn add_eth_chain(
        tx_conn: &mut DeferredTxConnection,
        address_id: &str,
        chain_id: eth::ChainId,
    ) -> Result<String, Error> {
        let chain_entity_id = m::Chain::fetch_or_create_eth_chain_id(tx_conn, chain_id)?;
        let asymmetric_key_id = Self::fetch_key_id(tx_conn.as_mut(), address_id)?;
        let address_entity = AddressEntity::builder()
            .asymmetric_key_id(&asymmetric_key_id)
            .chain_entity_id(&chain_entity_id)
            .build();
        let added_address_id =
            Self::fetch_or_create_for_eth_chain(tx_conn, &address_entity)?;
        Ok(added_address_id)
    }

    /// Create an Ethereum signing key and derived address.
    /// Returns the address id.
    pub fn create_eth_key_and_address(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        params: &CreateEthAddressParams,
    ) -> Result<String, Error> {
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
            .account_id(params.account_id)
            .dek_id(dek_id.as_str())
            .elliptic_curve(signing_key.curve)
            .public_key(public_key.as_ref())
            .encrypted_der(&encrypted_signing_key)
            .dapp_id(params.dapp_id)
            .is_account_wallet(params.is_account_wallet)
            .build()
            .insert(tx_conn)?;

        let checksum_address =
            eth::public_key_to_checksum_address(&signing_key.public_key)?;
        let address_id = NewAddress::builder()
            .asymmetric_key_id(key_id.as_str())
            .address(&*checksum_address)
            .build()
            .insert_eth(tx_conn, params.chain_id)?;

        Ok(address_id)
    }

    /// Fetch or create an address id for an Ethereum chain for an existing key.
    pub fn fetch_or_create_for_eth_chain(
        tx_conn: &mut DeferredTxConnection,
        address_entity: &AddressEntity,
    ) -> Result<String, Error> {
        match Self::exists(tx_conn.as_mut(), address_entity)? {
            Some(deterministic_id) => Ok(deterministic_id),
            None => {
                let public_key = m::AsymmetricKey::fetch_eth_public_key(
                    tx_conn.as_mut(),
                    address_entity.asymmetric_key_id,
                )?;
                let checksum_address = eth::public_key_to_checksum_address(&public_key)?;
                NewAddress::builder()
                    .asymmetric_key_id(address_entity.asymmetric_key_id)
                    .address(&*checksum_address)
                    .build()
                    .insert_eth_for_chain_entity(tx_conn, address_entity.chain_entity_id)
            }
        }
    }

    /// Fetch or create an address for an Ethereum chain for an existing key and re
    fn exists(
        conn: &mut SqliteConnection,
        address_entity: &AddressEntity,
    ) -> Result<Option<String>, Error> {
        use addresses::dsl as a;

        let deterministic_id = address_entity.deterministic_id()?;

        let exists: Option<bool> = addresses::table
            .filter(a::deterministic_id.eq(&*deterministic_id))
            .select(AsExpression::<Bool>::as_expression(true))
            .first(conn)
            .optional()?;

        Ok(exists.map(|_| deterministic_id))
    }

    /// Fetch the the address entity by id.
    pub fn fetch(conn: &mut SqliteConnection, address_id: &str) -> Result<Self, Error> {
        use addresses::dsl as a;

        let address: Self = addresses::table
            .filter(a::deterministic_id.eq(address_id))
            .select(ALL_COLUMNS)
            .first(conn)?;

        Ok(address)
    }

    pub fn fetch_account_id(
        conn: &mut SqliteConnection,
        address_id: &str,
    ) -> Result<String, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let account_id = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(a::deterministic_id.eq(address_id))
            .select(ak::account_id)
            .first(conn)?;

        Ok(account_id)
    }

    pub fn fetch_account_name(
        conn: &mut SqliteConnection,
        address_id: &str,
    ) -> Result<String, Error> {
        use accounts::dsl as ac;
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let account_name = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .inner_join(accounts::table.on(ak::account_id.eq(ac::deterministic_id)))
            .filter(a::deterministic_id.eq(address_id))
            .select(ac::name)
            .first(conn)?;

        Ok(account_name)
    }

    pub fn is_account_wallet(
        conn: &mut SqliteConnection,
        address_id: &str,
    ) -> Result<bool, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let is_account_wallet = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(a::deterministic_id.eq(address_id))
            .select(ak::is_account_wallet)
            .first(conn)?;

        Ok(is_account_wallet)
    }

    /// If this is a dapp key, return its human identifier.
    pub fn dapp_identifier(
        conn: &mut SqliteConnection,
        address_id: &str,
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
        address_id: &str,
    ) -> Result<String, Error> {
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
        address_id: &str,
    ) -> Result<String, Error> {
        use addresses::dsl as a;

        let address = addresses::table
            .filter(a::deterministic_id.eq(address_id))
            .select(a::address)
            .first(conn)?;

        Ok(address)
    }

    /// Fetch the address id by the checksum address if it exists.
    pub fn fetch_id_by_checksum_address(
        conn: &mut SqliteConnection,
        checksum_address: &str,
    ) -> Result<Option<String>, Error> {
        use addresses::dsl as a;

        let address_id = addresses::table
            .filter(a::address.eq(checksum_address))
            .select(a::deterministic_id)
            .first(conn)
            .optional()?;

        Ok(address_id)
    }

    /// Fetch the wallet address id for an Ethereum chain in an account.
    /// Assumes one wallet address per account per chain.
    pub fn fetch_eth_wallet_id(
        tx_conn: &mut DeferredTxConnection,
        account_id: &str,
        eth_chain_id: eth::ChainId,
    ) -> Result<String, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        let chain_id = m::Chain::fetch_or_create_eth_chain_id(tx_conn, eth_chain_id)?;

        let address_id = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(a::chain_id.eq(&*chain_id))
            .filter(ak::account_id.eq(account_id))
            .filter(ak::is_account_wallet.eq(true))
            .select(a::deterministic_id)
            .first(tx_conn.as_mut())?;

        Ok(address_id)
    }

    pub fn fetch_account_id_for_eth_address(
        connection: &mut SqliteConnection,
        checksum_address: &str,
    ) -> Result<Option<String>, Error> {
        use addresses::dsl as a;
        use asymmetric_keys::dsl as ak;

        use crate::protocols::eth::validate_checksum_address;

        validate_checksum_address(checksum_address)?;

        let account_id = addresses::table
            .inner_join(
                asymmetric_keys::table.on(ak::deterministic_id.eq(a::asymmetric_key_id)),
            )
            .filter(a::address.eq(checksum_address))
            .select(ak::account_id)
            .first(connection)
            .optional()?;

        Ok(account_id)
    }

    pub fn fetch_eth_signing_key(
        tx_conn: &mut DeferredTxConnection,
        keychain: &Keychain,
        address_id: &str,
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
        address_id: &str,
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
pub struct NewAddress<'a> {
    #[builder(setter(into))]
    pub asymmetric_key_id: &'a str,
    #[builder(setter(into))]
    pub address: &'a str,
}

impl<'a> NewAddress<'a> {
    /// Create a new asymmetric key and return its deterministic id.
    pub fn insert_eth(
        &self,
        tx_conn: &mut DeferredTxConnection,
        eth_chain_id: eth::ChainId,
    ) -> Result<String, Error> {
        let chain_entity_id =
            m::Chain::fetch_or_create_eth_chain_id(tx_conn, eth_chain_id)?;
        self.insert_eth_for_chain_entity(tx_conn, &chain_entity_id)
    }

    pub fn insert_eth_for_chain_entity(
        &self,
        tx_conn: &mut DeferredTxConnection,
        chain_entity_id: &str,
    ) -> Result<String, Error> {
        use addresses::dsl as a;

        let entity = AddressEntity {
            asymmetric_key_id: self.asymmetric_key_id,
            chain_entity_id,
        };
        let deterministic_id = entity.deterministic_id()?;
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
    pub asymmetric_key_id: &'a str,
    pub chain_entity_id: &'a str,
}

impl<'a> DeterministicId<'a, &'a str, U2> for AddressEntity<'a> {
    fn entity_name(&'a self) -> EntityName {
        EntityName::Address
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U2> {
        [self.asymmetric_key_id, self.chain_entity_id].into()
    }
}

#[derive(Clone, Debug, TypedBuilder)]
#[readonly::make]
pub struct ListAddressesForDappParams<'a> {
    pub account_id: &'a str,
    pub dapp_id: &'a str,
}

#[derive(Clone, Debug, TypedBuilder)]
#[readonly::make]
pub struct CreateEthAddressParams<'a> {
    pub account_id: &'a str,
    #[builder(setter(into))]
    pub chain_id: eth::ChainId,
    #[builder(default = None)]
    pub dapp_id: Option<&'a str>,
    #[builder(default = false)]
    pub is_account_wallet: bool,
}
