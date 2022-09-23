// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::Error;
use generic_array::{ArrayLength, GenericArray};
use lazy_static::lazy_static;
use strum_macros::{EnumIter, EnumString};

lazy_static! {
    static ref ENTITY_NAME_SPACE: &'static str = "org.sealvault.db.entity";
    /// 32-byte random string that lets us differentiate empty values in different positions.
    /// We use a random value as marker to make sure that it doesn't collide with any valid value
    /// unintentionally. We defend against adversarial attempts by returning an error if we get a
    /// a marker as a value.
    static ref EMPTY_MARKER: [u8; 32] =
        hex::decode("00572f578f78fb57992298bb3e20aa85bb5811f4f858aabc73c02e0f15b6c8cd")
            .expect("static hex is valid")
            .try_into()
            .expect("hex is expected length");
}

/// Deterministic ids make it easier to maintain referential integrity when syncing.
/// Synced DB entities MUST have a deterministic id as their PK.
/// DB entities that implement `DeterministicId` may only have a single unique constraint on the
/// table other than the PK. This unique constraint may not span nullable columns, as null values
/// are treated as not-equal by SQL which goes against the purpose of deterministic ids.
/// The purpose of this trait is to make it easy to review which entity uses what unique values to
/// determine its deterministic id.
/// See the developer docs for more background on deterministic ids.
pub trait DeterministicId<'a, T: AsRef<[u8]> + 'a, N: ArrayLength<T>> {
    /// The name of the database entity. Used as a prefix in the hash.
    fn entity_name(&'a self) -> EntityName;

    /// The name of the database entity. Used as a prefix in the hash.
    fn qualified_entity_name(&'a self) -> String {
        format!("{}.{}", *ENTITY_NAME_SPACE, self.entity_name())
    }

    /// Returns the column values for a row that define an entity. The deterministic id is derived
    /// from these values. The order matters and shouldn't change.
    /// New unique columns can be added to an entity, but only if they are nullable.
    /// We use `GenericArray`, because with this declaration, it's not possible to create a zero length
    /// array which would be a logic error and because it supports `IntoIter`.
    fn unique_columns(&'a self) -> GenericArray<T, N>;

    /// Compute a deterministic id for a database entity based on their unique columns.
    fn deterministic_id(&'a self) -> Result<String, Error> {
        let unique_columns = self.unique_columns();

        let mut hasher = blake3::Hasher::new();
        hasher.update(self.qualified_entity_name().as_bytes());
        for v in unique_columns {
            let v: &[u8] = v.as_ref();
            // Database contains no secrets in plain text, so no need for constant time eq.
            if v == *EMPTY_MARKER {
                // Important not to panic to don't let adversaries crash the app.
                return Err(Error::Retriable {
                    error:
                        "Adversarial attempt to cause deterministic id collision using \
                    marker value."
                            .into(),
                });
            }
            if v.is_empty() {
                hasher.update(&*EMPTY_MARKER);
            } else {
                hasher.update(v);
            }
        }
        let hash = hasher.finalize();
        let bytes = hash.as_bytes();
        Ok(data_encoding::BASE32_NOPAD.encode(bytes))
    }
}

#[derive(
    Copy, Clone, Debug, PartialEq, Eq, EnumIter, EnumString, strum_macros::Display,
)]
#[strum(serialize_all = "snake_case")]
pub enum EntityName {
    Account,
    AccountPicture,
    Address,
    AsymmetricKey,
    Chain,
    Dapp,
    DataEncryptionKey,
    DataMigration,
    #[cfg(test)]
    Mock,
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;
    use generic_array::GenericArray;

    struct UniqueValuesMock<'a, N: ArrayLength<&'a str>> {
        values: GenericArray<&'a str, N>,
        name: EntityName,
    }

    impl<'a, N: ArrayLength<&'a str>> UniqueValuesMock<'a, N> {
        fn new(values: GenericArray<&'a str, N>) -> Self {
            Self::new_with_name(EntityName::Mock, values)
        }

        fn new_with_name(name: EntityName, values: GenericArray<&'a str, N>) -> Self {
            Self { values, name }
        }
    }

    impl<'a, N: ArrayLength<&'a str>> DeterministicId<'a, &'a str, N>
        for UniqueValuesMock<'a, N>
    {
        fn entity_name(&'a self) -> EntityName {
            self.name
        }

        fn unique_columns(&'a self) -> GenericArray<&'a str, N> {
            self.values.clone()
        }
    }

    #[test]
    fn deterministic_id_expected_length() -> Result<()> {
        let unique_columns = UniqueValuesMock::new(["foo", "bar"].into());
        let id = unique_columns.deterministic_id()?;
        // 256-bit tag is 32 bytes and 32 bytes is 52 base32 characters without padding
        assert_eq!(id.len(), 52);
        Ok(())
    }

    #[test]
    fn all_values_hashed() -> Result<()> {
        let a = UniqueValuesMock::new(["foo", "bar", "baz"].into());
        let b = UniqueValuesMock::new(["foo", "bar", "fubar"].into());
        assert_ne!(a.deterministic_id(), b.deterministic_id());
        Ok(())
    }

    #[test]
    fn all_empty_equal() -> Result<()> {
        let a = UniqueValuesMock::new(["", ""].into());
        let b = UniqueValuesMock::new(["", ""].into());
        assert_eq!(a.deterministic_id(), b.deterministic_id());
        Ok(())
    }

    #[test]
    fn different_length_empties_not_equal() -> Result<()> {
        let one = UniqueValuesMock::new([""].into());
        let two = UniqueValuesMock::new(["", ""].into());
        assert_ne!(one.deterministic_id(), two.deterministic_id());
        Ok(())
    }

    #[test]
    fn empty_in_different_places_not_equal() -> Result<()> {
        let one = UniqueValuesMock::new(["", "foo"].into());
        let two = UniqueValuesMock::new(["foo", ""].into());
        assert_ne!(one.deterministic_id(), two.deterministic_id());
        Ok(())
    }

    #[test]
    fn uses_name() -> Result<()> {
        let a = UniqueValuesMock::new_with_name(EntityName::Mock, [""].into());
        let b = UniqueValuesMock::new_with_name(EntityName::Account, [""].into());
        assert_ne!(a.deterministic_id(), b.deterministic_id());
        Ok(())
    }

    #[test]
    fn uses_qualified_name() -> Result<()> {
        let name = EntityName::Mock;
        let a = UniqueValuesMock::new_with_name(name, [""].into());
        let mut hasher = blake3::Hasher::new();
        hasher.update(name.to_string().as_bytes());
        hasher.update(&*EMPTY_MARKER);
        let hash = hasher.finalize();
        let hash = hash.as_bytes();
        let hash = data_encoding::BASE64URL_NOPAD.encode(hash);
        assert_ne!(a.deterministic_id()?, hash);
        Ok(())
    }

    #[test]
    fn entity_name_snake_case() {
        let display = format!("{}", EntityName::DataEncryptionKey);
        assert_eq!(display, "data_encryption_key")
    }

    // TODO figure out why we can't make UniqueValuesMock generic over &str and &[u8; 32]
    struct UniqueArrayValuesMock<'a, N: ArrayLength<&'a [u8; 32]>> {
        values: GenericArray<&'a [u8; 32], N>,
    }

    impl<'a, N: ArrayLength<&'a [u8; 32]>> UniqueArrayValuesMock<'a, N> {
        fn new(values: GenericArray<&'a [u8; 32], N>) -> Self {
            Self { values }
        }
    }

    impl<'a, N: ArrayLength<&'a [u8; 32]>> DeterministicId<'a, &'a [u8; 32], N>
        for UniqueArrayValuesMock<'a, N>
    {
        fn entity_name(&'a self) -> EntityName {
            EntityName::Mock
        }
        fn unique_columns(&'a self) -> GenericArray<&'a [u8; 32], N> {
            self.values.clone()
        }
    }

    #[test]
    fn error_on_empty_marker_as_value() -> Result<()> {
        let a = UniqueArrayValuesMock::new([&*EMPTY_MARKER].into());
        let result = a.deterministic_id();
        assert!(matches!(
        result,
        Err(
            Error::Retriable {error})
            if error.to_string().to_lowercase().contains("adversarial")
        ));
        Ok(())
    }
}
