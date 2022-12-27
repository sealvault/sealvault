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
    strum_macros::IntoStaticStr,
)]
pub enum KeyName {
    // The serializations must not be changed as it's relied on to map from keychain/db.
    #[strum(serialize = "SK-KEY-ENCRYPTION-KEY")]
    SkKeyEncryptionKey,
    #[strum(serialize = "SK-DATA-ENCRYPTION-KEY")]
    SkDataEncryptionKey,
    #[strum(serialize = "BACKUP-PASSWORD")]
    BackupPassword,
    #[strum(serialize = "KDF-SECRET")]
    KdfSecret,
    #[strum(serialize = "ROOT-BACKUP-KEY")]
    RootBackupKey,
    #[strum(serialize = "DATABASE-BACKUP-DATA-ENCRYPTION-KEY")]
    DbBackupDataEncryptionKey,
    #[strum(serialize = "SECRET-KEY-BACKUP-KEY-ENCRYPTION-KEY")]
    SkBackupKeyEncryptionKey,
}

impl From<KeyName> for String {
    fn from(value: KeyName) -> Self {
        value.to_string()
    }
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

    #[test]
    fn serialize_sk_kek() {
        assert_eq!(
            KeyName::SkKeyEncryptionKey.to_string(),
            "SK-KEY-ENCRYPTION-KEY"
        );
    }
}
