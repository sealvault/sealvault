// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::db::deterministic_id::{DeterministicId, EntityName};
use crate::db::schema::{accounts, asymmetric_keys, dapps};
use crate::public_suffix_list::PublicSuffixList;
use diesel::prelude::*;
use diesel::SqliteConnection;
use generic_array::typenum::U1;
use generic_array::GenericArray;
use url::Url;

use crate::db::url_value::UrlValue;
use crate::db::DeferredTxConnection;
use crate::utils::rfc3339_timestamp;
use crate::Error;

#[derive(Clone, Debug, PartialEq, Eq, Queryable, Identifiable)]
#[diesel(primary_key(deterministic_id))]
pub struct Dapp {
    pub deterministic_id: String,
    pub identifier: String,
    pub url: UrlValue,
    pub created_at: String,
    pub updated_at: Option<String>,
}

type AllColumns = (
    dapps::deterministic_id,
    dapps::identifier,
    dapps::url,
    dapps::created_at,
    dapps::updated_at,
);

const ALL_COLUMNS: AllColumns = (
    dapps::deterministic_id,
    dapps::identifier,
    dapps::url,
    dapps::created_at,
    dapps::updated_at,
);

impl Dapp {
    pub fn all_columns() -> AllColumns {
        ALL_COLUMNS
    }

    /// List all dapps that have been added to an account.
    pub fn list_for_account(
        conn: &mut SqliteConnection,
        account_id: &str,
    ) -> Result<Vec<Self>, Error> {
        use asymmetric_keys::dsl as ak;
        use dapps::dsl as d;

        let dapps: Vec<Self> = asymmetric_keys::table
            .inner_join(dapps::table.on(ak::dapp_id.eq(d::deterministic_id.nullable())))
            .filter(ak::account_id.eq(account_id))
            .select(Self::all_columns())
            .load(conn)?;

        Ok(dapps)
    }

    /// Get the human-readable dapp identifier from an url.
    pub fn dapp_identifier(
        url: Url,
        public_suffix_list: &PublicSuffixList,
    ) -> Result<String, Error> {
        let dapp_entity = DappEntity::new(url, public_suffix_list)?;
        Ok(dapp_entity.identifier)
    }

    /// Create a dapp entity and return its deterministic id.
    /// The operation is idempotent.
    pub fn create_if_not_exists(
        tx_conn: &mut DeferredTxConnection,
        url: Url,
        public_suffix_list: &PublicSuffixList,
    ) -> Result<String, Error> {
        let dapp_entity = DappEntity::new(url, public_suffix_list)?;
        let dapp_id = dapp_entity.create_if_not_exists(tx_conn.as_mut())?;
        Ok(dapp_id)
    }

    /// Returns the dapp id if the dapp has been added to the account.
    pub fn fetch_id_for_account(
        conn: &mut SqliteConnection,
        url: Url,
        public_suffix_list: &PublicSuffixList,
        account_id: &str,
    ) -> Result<Option<String>, Error> {
        let dapp_entity = DappEntity::new(url, public_suffix_list)?;
        dapp_entity.fetch_id_for_account(conn, account_id)
    }
}

#[derive(Insertable)]
#[diesel(table_name = dapps)]
struct DappEntity {
    identifier: String,
    url: UrlValue,
}

impl DappEntity {
    fn new(url: Url, public_suffix_list: &PublicSuffixList) -> Result<Self, Error> {
        let origin = url.origin();
        let registrable_domain: Option<String> =
            public_suffix_list.registrable_domain(&origin)?.into();
        let identifier =
            registrable_domain.unwrap_or_else(|| origin.ascii_serialization());
        Ok(DappEntity {
            identifier,
            url: url.into(),
        })
    }

    /// Returns the dapp id if the dapp has been added to the account.
    fn fetch_id_for_account(
        &self,
        conn: &mut SqliteConnection,
        account_id: &str,
    ) -> Result<Option<String>, Error> {
        use accounts::dsl as a;
        use asymmetric_keys::dsl as ak;
        use dapps::dsl as d;
        use diesel::expression::AsExpression;
        use diesel::sql_types::Bool;

        let deterministic_id = self.deterministic_id()?;

        let maybe_exists: Option<bool> = asymmetric_keys::table
            .inner_join(accounts::table.on(ak::account_id.eq(a::deterministic_id)))
            .inner_join(dapps::table.on(ak::dapp_id.eq(d::deterministic_id.nullable())))
            .filter(a::deterministic_id.eq(account_id))
            .filter(d::deterministic_id.eq(&deterministic_id))
            // `exists` query is unstable
            .select(AsExpression::<Bool>::as_expression(true))
            .first(conn)
            .optional()?;

        match maybe_exists {
            Some(exists) if exists => Ok(Some(deterministic_id)),
            _ => Ok(None),
        }
    }

    /// Create a dapp entity and return its deterministic id.
    /// The operation is idempotent.
    fn create_if_not_exists(&self, conn: &mut SqliteConnection) -> Result<String, Error> {
        use dapps::dsl as d;

        let deterministic_id = self.deterministic_id()?;
        let created_at = rfc3339_timestamp();

        diesel::insert_into(dapps::table)
            .values((
                self,
                d::deterministic_id.eq(&deterministic_id),
                d::created_at.eq(&created_at),
            ))
            .on_conflict_do_nothing()
            .execute(conn)?;

        Ok(deterministic_id)
    }
}

impl<'a> DeterministicId<'a, &'a str, U1> for DappEntity {
    fn entity_name(&'a self) -> EntityName {
        EntityName::Dapp
    }

    fn unique_columns(&'a self) -> GenericArray<&'a str, U1> {
        let identifier = self.identifier.as_str();
        [identifier].into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dapp_identifier() {
        let psl: PublicSuffixList = Default::default();

        let url = Url::parse("https://www.example.com").unwrap();
        let identifier = Dapp::dapp_identifier(url, &psl).unwrap();
        assert_eq!(identifier, "example.com");
    }
}
