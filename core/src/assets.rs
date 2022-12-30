// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use rust_embed::{EmbeddedFile, RustEmbed};

use crate::{
    config::{PROFILE_PIC_EXTENSION, PROFILE_PIC_PREFIX},
    error::Error,
};

#[derive(RustEmbed)]
#[folder = "assets/"]
struct Asset;

fn load_asset(asset_path: &str) -> Result<EmbeddedFile, Error> {
    let embedded_file = Asset::get(asset_path).ok_or_else(|| Error::Fatal {
        error: format!("Asset not found at path: '{}'", asset_path),
    })?;
    Ok(embedded_file)
}

pub(super) fn load_binary(asset_path: &str) -> Result<Vec<u8>, Error> {
    Ok(load_asset(asset_path)?.data.to_vec())
}

pub(super) fn load_asset_as_string(asset_path: &str) -> Result<String, Error> {
    let embedded_file = load_asset(asset_path)?;
    let str =
        std::str::from_utf8(embedded_file.data.as_ref()).map_err(|err| Error::Fatal {
            error: err.to_string(),
        })?;
    Ok(str.to_string())
}

/// Load a profile picture image as bytes by its name (file name without extension).
pub fn load_profile_pic(name: &str) -> Result<Vec<u8>, Error> {
    let asset_path = format!("{}/{}{}", PROFILE_PIC_PREFIX, name, PROFILE_PIC_EXTENSION);
    let embedded_file = load_asset(&asset_path)?;
    Ok(Vec::from(embedded_file.data))
}

/// List available profile picture names.
pub fn list_profile_pics() -> Vec<String> {
    let prefix = format!("{}/", PROFILE_PIC_PREFIX);
    Asset::iter()
        .filter_map(|p| p.strip_prefix(&prefix).map(|p| p.to_string()))
        .filter_map(|p| {
            p.strip_suffix(&PROFILE_PIC_EXTENSION)
                .map(|p| p.to_string())
        })
        .collect()
}

type Replacement<'a> = (&'a str, &'a str);

/// Load asset replacing the first occurrence each replacement.
pub(super) fn load_asset_with_replacements<'a>(
    asset_path: &str,
    replacements: impl Iterator<Item = &'a Replacement<'a>>,
) -> Result<String, Error> {
    let mut text = load_asset_as_string(asset_path)?;
    for (from, to) in replacements {
        text = text.replacen(from, to, 1);
    }
    Ok(text)
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;

    #[test]
    fn lists_profile_pics() -> Result<()> {
        let profile_pics = list_profile_pics();

        dbg!(profile_pics.clone());

        assert_eq!(profile_pics.len(), 10);
        assert!(profile_pics.contains(&"seal-0".to_string()));
        assert!(profile_pics.contains(&"seal-9".to_string()));

        Ok(())
    }

    #[test]
    fn loads_profile_pic() -> Result<()> {
        let data = load_profile_pic("seal-1")?;
        assert!(data.len() > 1000);

        Ok(())
    }
}
