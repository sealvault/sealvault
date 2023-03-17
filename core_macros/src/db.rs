// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

/// Implement `ToSql` using the type's `to_string` method and `FromSql` using the type's `FromStr`
/// implementation.
#[macro_export]
macro_rules! sql_text {
    ($type_name:ident) => {
        impl diesel::deserialize::FromSql<diesel::sql_types::Text, diesel::sqlite::Sqlite>
            for $type_name
        {
            fn from_sql(
                bytes: diesel::backend::RawValue<diesel::sqlite::Sqlite>,
            ) -> diesel::deserialize::Result<Self> {
                use std::string::String;

                use diesel::{deserialize::FromSql, sql_types::Text, sqlite::Sqlite};

                let s = <String as FromSql<Text, Sqlite>>::from_sql(bytes)?;
                let result: $type_name = s.parse()?;
                Ok(result)
            }
        }

        impl diesel::serialize::ToSql<diesel::sql_types::Text, diesel::sqlite::Sqlite>
            for $type_name
        {
            fn to_sql(
                &self,
                out: &mut diesel::serialize::Output<diesel::sqlite::Sqlite>,
            ) -> diesel::serialize::Result {
                let s = self.to_string();
                out.set_value(s);
                Ok(diesel::serialize::IsNull::No)
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use anyhow::Result;
    use derive_more::{AsRef, Display, Into};
    use diesel::{
        deserialize::FromSqlRow,
        dsl,
        expression::{AsExpression, TypedExpressionType},
        query_builder::{AsQuery, QueryId},
        query_dsl::LoadQuery,
        select,
        sql_types::{HasSqlType, SingleValue, SqlType, Text},
        Connection, IntoSql, Queryable, RunQueryDsl, SqliteConnection,
    };

    pub fn connection() -> SqliteConnection {
        let mut conn = SqliteConnection::establish(":memory:").unwrap();
        diesel::sql_query("PRAGMA foreign_keys = ON")
            .execute(&mut conn)
            .unwrap();
        conn
    }

    /// Test that serializing and deserializing to/from SQL results in the same value.
    /// Based on: https://github.com/diesel-rs/diesel/blob/25afffb6f0d1537a496ffbc1842102aba7936dce/diesel_tests/tests/types_roundtrip.rs#L18-L53
    pub fn test_type_round_trip<ST, T>(value: T) -> Result<()>
    where
        ST: QueryId + SqlType + TypedExpressionType + SingleValue,
        <SqliteConnection as Connection>::Backend: HasSqlType<ST>,
        T: AsExpression<ST>
            + FromSqlRow<ST, <SqliteConnection as Connection>::Backend>
            + Queryable<ST, <SqliteConnection as Connection>::Backend>
            + Clone
            + Eq
            + ::std::fmt::Debug
            + 'static,
        for<'a> dsl::BareSelect<<T as AsExpression<ST>>::Expression>:
            AsQuery + LoadQuery<'a, SqliteConnection, T>,
    {
        let connection = &mut connection();
        let query = select(value.clone().into_sql::<ST>());
        let result = query.get_result::<T>(connection)?;
        assert_eq!(&value, &result);
        Ok(())
    }

    #[derive(
        Debug, Display, Clone, Eq, PartialEq, Into, AsRef, AsExpression, FromSqlRow,
    )]
    #[diesel(sql_type = Text)]
    #[repr(transparent)]
    struct TestText(String);

    impl FromStr for TestText {
        type Err = anyhow::Error;

        fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
            Ok(Self(s.into()))
        }
    }

    sql_text!(TestText);

    #[test]
    fn test_sql_text() -> Result<()> {
        let text = TestText::from_str("hello")?;
        test_type_round_trip::<Text, _>(text)?;
        Ok(())
    }
}