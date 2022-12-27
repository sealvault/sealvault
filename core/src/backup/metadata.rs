// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{fs, str::FromStr};

use lazy_static::lazy_static;
use olpc_cjson::CanonicalFormatter;
use regex::Regex;
use serde::{Deserialize, Serialize};
use typed_builder::TypedBuilder;

use crate::{
    backup::backup_scheme::BackupScheme,
    device::{DeviceIdentifier, DeviceName, OperatingSystem},
    utils::unix_timestamp,
    Error,
};

lazy_static! {
    static ref BACKUP_FILE_NAME_REGEX: Regex =
        Regex::new(r"^sealvault_backup_(?P<scheme>[A-Za-z0-9-]+)_(?P<os>[A-Za-z0-9-]+)_(?P<timestamp>\d+)_(?P<device_id>[A-Za-z0-9-]+)_(?P<version>\d+)\.zip$").expect("static is ok");
}

/// Saved as a plaintext json file along with the encrypted backup.
/// More info: https://sealvault.org/dev-docs/design/backup/#backup-contents
#[derive(Debug, PartialEq, Serialize, Deserialize, TypedBuilder)]
pub struct BackupMetadata {
    /// The backup implementation version
    pub backup_scheme: BackupScheme,
    /// The backup version from the database. Monotonically increasing integer within a device.
    pub backup_version: i64,
    /// Unix timestamp
    #[builder(default_code = "unix_timestamp()")]
    pub timestamp: i64,
    pub device_id: DeviceIdentifier,
    pub device_name: DeviceName,
    #[builder(default)]
    pub operating_system: OperatingSystem,
    /// Base-64 encoded KDF nonce
    #[builder(setter(into))]
    pub kdf_nonce: String,
}

impl BackupMetadata {
    pub(in crate::backup) fn backup_file_name(&self) -> String {
        format!(
            "sealvault_backup_{}_{}_{}_{}_{}.zip",
            self.backup_scheme,
            self.operating_system,
            self.timestamp,
            self.device_id,
            self.backup_version
        )
    }

    /// Use this for a canonical serialization of the backup metadata to make sure that the
    /// associated data in the AEAD matches.
    pub fn canonical_json(&self) -> Result<Vec<u8>, Error> {
        let mut buf = Vec::new();
        let mut ser =
            serde_json::Serializer::with_formatter(&mut buf, CanonicalFormatter::new());
        self.serialize(&mut ser).map_err(|_| Error::Fatal {
            error: "Failed to serialize backup metadata.".into(),
        })?;
        Ok(buf)
    }
}

#[derive(Debug, PartialEq)]
pub(in crate::backup) struct MetadataFromFileName {
    pub timestamp: i64,
    pub os: OperatingSystem,
    pub device_id: DeviceIdentifier,
    pub backup_version: i64,
}

impl FromStr for MetadataFromFileName {
    type Err = Error;

    fn from_str(file_name: &str) -> Result<Self, Self::Err> {
        let captures =
            BACKUP_FILE_NAME_REGEX
                .captures(file_name)
                .ok_or_else(|| Error::Fatal {
                    error: format!("Invalid backup file name format: '{file_name}'"),
                })?;

        let timestamp = parse_field_from_backup_file_name(&captures, "timestamp")?;
        let os = parse_field_from_backup_file_name(&captures, "os")?;
        let device_id = parse_field_from_backup_file_name(&captures, "device_id")?;
        let backup_version = parse_field_from_backup_file_name(&captures, "version")?;

        Ok(MetadataFromFileName {
            timestamp,
            os,
            backup_version,
            device_id,
        })
    }
}

impl TryFrom<&fs::DirEntry> for MetadataFromFileName {
    type Error = Error;

    fn try_from(dir_entry: &fs::DirEntry) -> Result<Self, Self::Error> {
        let file_name = dir_entry.file_name();
        let file_name = file_name.to_str().ok_or_else(|| Error::Fatal {
            error: "Invalid characters in backup file name".into(),
        })?;
        file_name.parse()
    }
}

fn parse_field_from_backup_file_name<T>(
    captures: &regex::Captures,
    name: &str,
) -> Result<T, Error>
where
    T: FromStr,
    Error: From<<T as FromStr>::Err>,
{
    let group = captures.name(name).ok_or_else(|| Error::Fatal {
        error: format!("No {name} in backup file name"),
    })?;
    let value: T = group.as_str().parse()?;
    Ok(value)
}
