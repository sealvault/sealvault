// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashMap, env, fs, process::Command};

use anyhow::Result;
use strum::IntoEnumIterator;
use tempfile::tempdir;
use uniffi_sealvault_core::{protocols::eth::ChecksumAddress, ChainId};

const TOKENS_REPO: &str = "https://github.com/sealvault/assets";
const BLOCKCHAINS_DIR: &str = "blockchains";
const ASSETS_DIR: &str = "assets";
const TOKEN_INFO: &str = "info.json";

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    let out_path = args.get(1).expect("output path");

    let workdir = tempdir()?;

    // SSL issues with git2 on Apple Silicon hence the CLI approach
    let status = Command::new("git")
        .arg("clone")
        .arg("--depth")
        .arg("1")
        .arg(TOKENS_REPO)
        .args(workdir.path().to_str())
        .status()?;
    assert!(status.success());

    let output = Command::new("git")
        .arg("rev-parse")
        .arg("--short")
        .arg("HEAD")
        .current_dir(&workdir)
        .output()?;
    assert!(output.status.success());
    let commit_hash = String::from_utf8(output.stdout)?.trim().to_string();

    let blockchains_dir = workdir.path().join(BLOCKCHAINS_DIR);

    let mut fungible_tokens: HashMap<ChainId, Vec<ChecksumAddress>> = Default::default();

    for chain_id in ChainId::iter() {
        if let Some(asset_name) = chain_id.trust_wallet_asset_name() {
            let tokens_dir = blockchains_dir.join(asset_name).join(ASSETS_DIR);
            for entry in tokens_dir.read_dir()? {
                let entry = entry?;
                let path = entry.path();
                let token_info = path.join(TOKEN_INFO);
                let file = fs::File::open(token_info)?;
                let token_info: TokenInfo = serde_json::from_reader(file)?;
                let checksum_address: ChecksumAddress = token_info.id.parse()?;
                fungible_tokens
                    .entry(chain_id)
                    .or_default()
                    .push(checksum_address);
            }
        }
    }

    let common_tokens = CommonTokens {
        commit_hash,
        fungible_tokens,
    };

    // Save common tokens as json to out_path
    let file = fs::File::create(out_path)?;
    serde_json::to_writer_pretty(file, &common_tokens)?;
    println!("Saved common tokens to {out_path}");

    Ok(())
}

#[derive(Debug, serde::Deserialize, serde::Serialize)]
struct CommonTokens {
    /// The commit hash of https://github.com/sealvault/assets from which the tokens were compiled
    commit_hash: String,
    /// The common fungible tokens for each chain
    fungible_tokens: HashMap<ChainId, Vec<ChecksumAddress>>,
}

#[derive(Debug, serde::Deserialize)]
struct TokenInfo {
    id: String,
}
