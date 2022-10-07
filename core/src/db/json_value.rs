// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter};

use diesel::{deserialize::FromSql, serialize::ToSql, sql_types::Text, sqlite::Sqlite};
use olpc_cjson::CanonicalFormatter;
use serde::{de::DeserializeOwned, Serialize};

use crate::Error;

/// Wrapper to let us implement Diesel `FromSql` and `ToSql` for `serde_json::Value`.
#[derive(
    Clone,
    PartialEq,
    Eq,
    // Diesel traits
    AsExpression,
    FromSqlRow,
)]
#[diesel(sql_type = diesel::sql_types::Text)]
pub struct JsonValue(serde_json::Value);

impl JsonValue {
    pub fn new(value: serde_json::Value) -> Self {
        Self(value)
    }

    // Trait bounds are too wide for generic `TryFrom` implementations.
    // We could add derive macros for specific `TryFrom` implementations
    // of types that should be turned into `JsonValue`, but this is simpler.

    pub fn convert_into<T: DeserializeOwned>(self) -> Result<T, Error> {
        serde_json::from_value(self.0).map_err(|_| Error::Fatal {
            error: "Failed to deserialize json value".into(),
        })
    }

    pub fn convert_from<T: Serialize>(from: T) -> Result<Self, Error> {
        // This conversion should never fail, hence the unexpected error.
        let value = serde_json::to_value(from).map_err(|_err| Error::Fatal {
            error: "Failed to convert Serialize type to json value".into(),
        })?;
        Ok(JsonValue::new(value))
    }

    /// We don't implement `serde::ser::Serialize`, because that takes the serializer as argument
    /// and it's important to use canonical serialization to allow unique constraints on JSON
    /// fields. Sqlite stores JSON as ordinary strings, but allows querying them with JSON
    /// operators.
    pub fn serialize(&self) -> Result<String, Error> {
        let mut buf = Vec::new();
        let mut ser =
            serde_json::Serializer::with_formatter(&mut buf, CanonicalFormatter::new());
        self.0.serialize(&mut ser).map_err(|_| Error::Fatal {
            error: "Failed to serialize json value.".into(),
        })?;

        // .expect("serializing serde_json::Value never fails.");
        let s = std::str::from_utf8(&buf).map_err(|_| Error::Fatal {
            error: "Json serializer produced invalid utf8.".into(),
        })?;
        Ok(s.into())
    }
}

impl Debug for JsonValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let json_type = match &self.0 {
            serde_json::Value::Null => "Null",
            serde_json::Value::Bool(_) => "Bool",
            serde_json::Value::Number(_) => "Number",
            serde_json::Value::String(_) => "String",
            serde_json::Value::Array(_) => "Array",
            serde_json::Value::Object(_) => "Object",
        };
        // This is an opaque type. Don't log actual values to avoid leaking secrets by accident.
        f.debug_struct("JsonValue").field("0", &json_type).finish()
    }
}

impl From<serde_json::Value> for JsonValue {
    fn from(value: serde_json::Value) -> Self {
        Self::new(value)
    }
}

impl FromSql<Text, Sqlite> for JsonValue {
    fn from_sql(
        bytes: diesel::backend::RawValue<Sqlite>,
    ) -> diesel::deserialize::Result<Self> {
        let s = <String as FromSql<Text, Sqlite>>::from_sql(bytes)?;
        Ok(Self(serde_json::from_str(&s)?))
    }
}

impl ToSql<Text, Sqlite> for JsonValue {
    fn to_sql(
        &self,
        out: &mut diesel::serialize::Output<Sqlite>,
    ) -> diesel::serialize::Result {
        let s = self.serialize()?;
        out.set_value(s);
        Ok(diesel::serialize::IsNull::No)
    }
}
