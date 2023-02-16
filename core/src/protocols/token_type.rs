// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FungibleTokenType {
    Native,
    Custom,
}

use std::str::FromStr;

use diesel::{deserialize::FromSql, serialize::ToSql, sqlite::Sqlite};

#[derive(
    Clone,
    Debug,
    PartialEq,
    Eq,
    strum_macros::EnumString,
    strum_macros::Display,
    strum_macros::IntoStaticStr,
    // Diesel traits
    AsExpression,
    FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Text)]
#[strum(serialize_all = "snake_case")]
pub enum TokenType {
    Fungible,
    Nft,
}

// TODO (abiro) add derive macro
impl FromSql<diesel::sql_types::Text, Sqlite> for TokenType {
    fn from_sql(
        bytes: diesel::backend::RawValue<Sqlite>,
    ) -> diesel::deserialize::Result<Self> {
        let s = <String as FromSql<diesel::sql_types::Text, Sqlite>>::from_sql(bytes)?;
        Ok(Self::from_str(&s)?)
    }
}

impl ToSql<diesel::sql_types::Text, Sqlite> for TokenType {
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
        assert_eq!(TokenType::Fungible.to_string(), "fungible");
    }

    #[test]
    fn from_string() -> Result<()> {
        let nft = TokenType::try_from("nft")?;

        assert_eq!(nft, TokenType::Nft);

        Ok(())
    }
}
