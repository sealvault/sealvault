// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::Error;
use diesel::deserialize::FromSql;
use diesel::serialize::ToSql;
use diesel::sqlite::Sqlite;
use k256::elliptic_curve::pkcs8;
use k256::elliptic_curve::pkcs8::AssociatedOid as _;
use std::str::FromStr;

#[derive(
    Copy,
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
pub enum EllipticCurve {
    Secp256k1,
}

impl TryFrom<pkcs8::ObjectIdentifier> for EllipticCurve {
    type Error = Error;

    fn try_from(oid: pkcs8::ObjectIdentifier) -> Result<Self, Self::Error> {
        match oid {
            k256::Secp256k1::OID => Ok(EllipticCurve::Secp256k1),
            _ => Err(Error::Fatal {
                error: format!("Unsupported PKCS8 object identifier: '{}'", oid),
            }),
        }
    }
}

type SqlText = diesel::sql_types::Text;

impl FromSql<SqlText, Sqlite> for EllipticCurve {
    fn from_sql(
        bytes: diesel::backend::RawValue<Sqlite>,
    ) -> diesel::deserialize::Result<Self> {
        let s = <String as FromSql<SqlText, Sqlite>>::from_sql(bytes)?;
        Ok(Self::from_str(&s)?)
    }
}

impl ToSql<SqlText, Sqlite> for EllipticCurve {
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
    use super::*;

    #[test]
    fn to_string() {
        assert_eq!(EllipticCurve::Secp256k1.to_string(), "Secp256k1")
    }
}
