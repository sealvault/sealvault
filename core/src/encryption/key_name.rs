// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

#[derive(
    Copy,
    Clone,
    Debug,
    Hash,
    PartialEq,
    Eq,
    strum_macros::AsRefStr,
    strum_macros::Display,
    strum_macros::EnumString,
    strum_macros::EnumIter,
)]
pub enum KeyName {
    // Secret key
    #[strum(serialize = "SK-KEY-ENCRYPTION-KEY")]
    SkKeyEncryptionKey,
    #[strum(serialize = "SK-DATA-ENCRYPTION-KEY")]
    SkDataEncryptionKey,
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use strum::IntoEnumIterator;

    use super::*;

    #[test]
    fn unique_to_strings() {
        let count = KeyName::iter().count();
        let set: HashSet<String> = KeyName::iter().map(|kn| kn.to_string()).collect();
        assert_eq!(count, set.len());
    }
}
