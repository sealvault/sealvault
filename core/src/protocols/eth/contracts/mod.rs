// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
use ethers::contract::abigen;

abigen!(
    ERC20Contract,
    r#"[
        function balanceOf(address account) external view returns (uint256)
        function decimals() public view virtual override returns (uint8)
        function transfer(address to, uint256 amount) public virtual override returns (bool)
        event Transfer(address indexed from, address indexed to, uint256 value)
    ]"#,
    event_derives(serde::Deserialize, serde::Serialize)
);

#[cfg(test)]
pub mod test_util {
    use crate::protocols::eth::ChainId;
    use anyhow::Result;
    use ethers::contract::ContractFactory;
    use ethers::core::types::Address;
    use ethers::core::utils::{Anvil, AnvilInstance};
    use ethers::middleware::SignerMiddleware;
    use ethers::providers::{Http, Provider};
    use ethers::signers::coins_bip39::English;
    use ethers::signers::{LocalWallet, MnemonicBuilder, Signer};
    use ethers::solc::{Artifact, Project, ProjectPathsConfig};
    use std::path::PathBuf;
    use std::sync::Arc;
    use std::time::Duration;

    const MNEMONIC: &str = "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about";

    pub struct TestContractDeployer {
        pub anvil_instance: AnvilInstance,
    }

    impl TestContractDeployer {
        pub fn init(chain_id: ChainId) -> Self {
            let anvil_instance = Anvil::new()
                .chain_id(chain_id as u64)
                .mnemonic(MNEMONIC)
                .spawn();
            Self { anvil_instance }
        }

        pub fn endpoint(&self) -> String {
            self.anvil_instance.endpoint()
        }

        pub fn deployer_wallet(&self) -> LocalWallet {
            MnemonicBuilder::<English>::default()
                .phrase(MNEMONIC)
                .build()
                .unwrap()
        }

        pub fn provider(&self) -> Provider<Http> {
            let endpoint = self.endpoint();
            Provider::<Http>::try_from(endpoint)
                .unwrap()
                .interval(Duration::from_millis(10u64))
        }

        /// Deploy FungibleTokenTest ERC20 contract on local Anvil node.
        /// Returns the contract address.
        /// Based on https://github.com/gakonst/ethers-rs/blob/69f24e03efca769ed2acc96b95029b3f07fd5493/examples/contract_human_readable.rs
        pub async fn deploy_fungible_token_test_contract(&self) -> Result<Address> {
            // Compile FungibleTokenTest contract
            let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("src/protocols/eth/contracts/fungible_token_test");
            let paths = ProjectPathsConfig::builder()
                .root(&root)
                .sources(&root)
                .build()
                .unwrap();
            let project = Project::builder()
                .paths(paths)
                .ephemeral()
                .no_artifacts()
                .build()
                .unwrap();
            // TODO compilation takes around two seconds when running here, but only ~200ms when
            // invoking solc directly.
            let output = project.compile().unwrap();
            let contract = output
                .find_first("FungibleTokenTest")
                .expect("could not find contract")
                .clone();
            let (abi, bytecode, _) = contract.into_parts();

            let chain_id = self.anvil_instance.chain_id();

            // Deploy FungibleTokenTest contract
            let wallet: LocalWallet = self.deployer_wallet();
            let provider = self.provider();
            let client = SignerMiddleware::new(provider, wallet.with_chain_id(chain_id));
            let client = Arc::new(client);
            let factory =
                ContractFactory::new(abi.unwrap(), bytecode.unwrap(), client.clone());
            let contract = factory.deploy(())?.send().await?;

            Ok(contract.address())
        }
    }
}
