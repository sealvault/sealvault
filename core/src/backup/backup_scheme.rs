// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use serde::{Deserialize, Serialize};

/// The backup scheme version.
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
    Serialize,
    Deserialize,
)]
#[strum(serialize_all = "lowercase")]
pub enum BackupScheme {
    V1,
}
