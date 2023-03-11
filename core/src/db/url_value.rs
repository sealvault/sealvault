// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{fmt::Debug, str::FromStr};

use core_macros::sql_text;
use url::Url;

use crate::Error;

/// Wrapper to let us implement Diesel FromSql and ToSql for url::Url.
/// Urls stored in the DB are assumed to not to contain secrets, so we derive Debug.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    derive_more::Display,
    // Diesel traits
    AsExpression,
    FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Text)]
#[repr(transparent)]
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

impl FromStr for UrlValue {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(s.parse()?))
    }
}

sql_text!(UrlValue);
