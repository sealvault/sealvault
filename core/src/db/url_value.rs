// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::deserialize::FromSql;
use diesel::serialize::ToSql;
use diesel::sql_types::Text;
use diesel::sqlite::Sqlite;
use std::fmt::Debug;
use url::Url;

/// Wrapper to let us implement Diesel FromSql and ToSql for url::Url.
/// Urls stored in the DB are assumed to not to contain secrets, so we derive Debug.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    // Diesel traits
    AsExpression,
    FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Text)]
pub struct UrlValue(Url);

impl From<Url> for UrlValue {
    fn from(url: Url) -> Self {
        Self(url)
    }
}

impl From<UrlValue> for Url {
    fn from(value: UrlValue) -> Self {
        value.0
    }
}

impl From<&UrlValue> for String {
    fn from(value: &UrlValue) -> Self {
        value.0.to_string()
    }
}

impl FromSql<Text, Sqlite> for UrlValue {
    fn from_sql(
        bytes: diesel::backend::RawValue<Sqlite>,
    ) -> diesel::deserialize::Result<Self> {
        let s = <String as FromSql<Text, Sqlite>>::from_sql(bytes)?;
        let url: Url = s.parse()?;
        Ok(url.into())
    }
}

impl ToSql<Text, Sqlite> for UrlValue {
    fn to_sql(
        &self,
        out: &mut diesel::serialize::Output<Sqlite>,
    ) -> diesel::serialize::Result {
        let s = self.0.to_string();
        out.set_value(s);
        Ok(diesel::serialize::IsNull::No)
    }
}
