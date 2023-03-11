// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

/// Implement `ToSql` using the type's `to_string` method and `FromSql` using the type's `FromStr`
/// implementation.
// #[macro_export]
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
        serialize::{Output, ToSql},
        sql_types::Text,
        sqlite::{Sqlite, SqliteBindValue},
    };

    #[derive(Debug, Display, Clone, Eq, PartialEq, Into, AsRef)]
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
    fn test_string() -> Result<()> {
        let s = "hello";
        let text = TestText::from_str(s)?;

        let value: SqliteBindValue = None::<String>.into();
        let mut metadata = ();
        let mut output = Output::<Sqlite>::new(value, &mut metadata);
        let is_null =
            <TestText as ToSql<Text, Sqlite>>::to_sql(&text, &mut output).unwrap();

        assert_eq!(is_null, diesel::serialize::IsNull::No);
        // TODO test value pending https://github.com/diesel-rs/diesel/discussions/3538

        Ok(())
    }
}
