// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use derive_more::{AsRef, Display, Into};
use lazy_static::lazy_static;
use regex::Regex;
use serde::{Deserialize, Serialize};

use crate::Error;

#[derive(
    Debug, Display, Clone, Eq, PartialEq, Hash, Into, AsRef, Serialize, Deserialize,
)]
#[serde(try_from = "String")]
#[serde(into = "String")]
#[repr(transparent)]
pub struct DeviceIdentifier(String);

lazy_static! {
    // Device id is included in backup file name where separator is '_'.
    static ref DEVICE_ID_REGEX: Regex =
        Regex::new(r"^[A-Za-z0-9-]+$").expect("static is ok");
}

impl TryFrom<String> for DeviceIdentifier {
    type Error = Error;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        if DEVICE_ID_REGEX.is_match(&value) {
            Ok(Self(value))
        } else {
            Err(Error::Fatal {
                error: "Invalid device identifier: '{value}'".into(),
            })
        }
    }
}

#[derive(Debug, Display, Clone, Eq, PartialEq, AsRef, Serialize, Deserialize)]
#[serde(transparent)]
#[repr(transparent)]
pub struct OperatingSystem(String);

impl Default for OperatingSystem {
    fn default() -> Self {
        let os = if std::env::consts::OS.is_empty() {
            "unknown-os"
        } else {
            std::env::consts::OS
        };
        Self(os.into())
    }
}
