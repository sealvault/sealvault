// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashMap, env, fs, path::Path, process::Command};

use anyhow::Result;
use strum::IntoEnumIterator;
use tempfile::tempdir;
use uniffi_sealvault_core::protocols::eth::{
    ChainId, ChecksumAddress, CommonTokenInfo, CommonTokens,
};
use url::Url;

const TOKENS_REPO: &str = "https://github.com/sealvault/assets";
const BLOCKCHAINS_DIR: &str = "blockchains";
const ASSETS_DIR: &str = "assets";
const TOKEN_INFO: &str = "info.json";
const TOKEN_LIST: &str = "tokenlist.json";

fn github_logo_uri(chain_id: ChainId, contract_address: &ChecksumAddress) -> Result<Url> {
    let blockchain = chain_id
        .trust_wallet_asset_name()
        .expect("trust wallet asset name");
    let url: Url = format!(
        "https://raw.githubusercontent.com/sealvault/assets/master/blockchains/{blockchain}/assets/{contract_address}/logo.png"
    ).parse()?;
    Ok(url)
}

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

    let mut fungible_tokens: HashMap<ChainId, Vec<CommonTokenInfo>> = Default::default();

    for chain_id in ChainId::iter() {
        if let Some(chain_name) = chain_id.trust_wallet_asset_name() {
            let chain_dir = blockchains_dir.join(chain_name);
            let token_list = chain_dir.join(TOKEN_LIST);
            let tokens_dir = chain_dir.join(ASSETS_DIR);
            // If there is a precompiled list of assets by Trust Wallet for the chain, use that,
            // otherwise compile the assets ourselves.
            if token_list.exists() {
                let TrustWalletTokenList { tokens } =
                    serde_json::from_reader(fs::File::open(token_list)?)?;
                let tokens = tokens
                    .into_iter()
                    .map(|TrustWalletTokenListItem { address, logo_uri }| {
                        CommonTokenInfo {
                            address,
                            logo_uri: Some(logo_uri),
                        }
                    })
                    .collect::<Vec<_>>();
                fungible_tokens.insert(chain_id, tokens);
            } else {
                tokens_without_token_list(&mut fungible_tokens, chain_id, &tokens_dir)?;
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

fn tokens_without_token_list(
    fungible_tokens: &mut HashMap<ChainId, Vec<CommonTokenInfo>>,
    chain_id: ChainId,
    tokens_dir: &Path,
) -> Result<()> {
    for entry in tokens_dir.read_dir()? {
        let entry = entry?;
        let path = entry.path();
        let token_info = path.join(TOKEN_INFO);
        let file = fs::File::open(token_info)?;
        let TrustWalletTokenInfo { id } = serde_json::from_reader(file)?;

        let address: ChecksumAddress = id.parse()?;

        let logo_uri = github_logo_uri(chain_id, &address)?;
        // HEAD request to check if logo uri exists
        let response = reqwest::blocking::Client::new()
            .head(logo_uri.clone())
            .send()?;
        let logo_uri = if response.error_for_status().is_err() {
            None
        } else {
            Some(logo_uri)
        };

        let token_info = CommonTokenInfo { address, logo_uri };
        fungible_tokens
            .entry(chain_id)
            .or_default()
            .push(token_info);
    }
    Ok(())
}

#[derive(Debug, serde::Deserialize)]
struct TrustWalletTokenInfo {
    id: String,
}

#[derive(Debug, serde::Deserialize)]
struct TrustWalletTokenList {
    tokens: Vec<TrustWalletTokenListItem>,
}

#[derive(Debug, serde::Deserialize)]
struct TrustWalletTokenListItem {
    address: ChecksumAddress,
    #[serde(rename = "logoURI")]
    logo_uri: Url,
}
