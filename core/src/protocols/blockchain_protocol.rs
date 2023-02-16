// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::str::FromStr;

use diesel::{deserialize::FromSql, serialize::ToSql, sqlite::Sqlite};

#[derive(
    Clone,
    Debug,
    PartialEq,
    Eq,
    strum_macros::EnumString,
    strum_macros::Display,
    // Diesel traits
    AsExpression,
    FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Text)]
#[strum(serialize_all = "snake_case")]
pub enum BlockchainProtocol {
    Ethereum,
}

// TODO (abiro) add derive macro
impl FromSql<diesel::sql_types::Text, Sqlite> for BlockchainProtocol {
    fn from_sql(
        bytes: diesel::backend::RawValue<Sqlite>,
    ) -> diesel::deserialize::Result<Self> {
        let s = <String as FromSql<diesel::sql_types::Text, Sqlite>>::from_sql(bytes)?;
        Ok(Self::from_str(&s)?)
    }
}

impl ToSql<diesel::sql_types::Text, Sqlite> for BlockchainProtocol {
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

    #[test]
    fn to_string() {
        assert_eq!(BlockchainProtocol::Ethereum.to_string(), "ethereum");
    }

    #[test]
    fn from_string() -> Result<()> {
        let bp = BlockchainProtocol::try_from("ethereum")?;

        assert_eq!(bp, BlockchainProtocol::Ethereum);

        Ok(())
    }
}
