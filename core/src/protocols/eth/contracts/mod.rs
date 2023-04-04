// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.
use ethers::contract::abigen;

abigen!(
    ERC20Contract,
    r#"[
        function totalSupply() external view returns (uint256)
        function balanceOf(address account) external view returns (uint256)
        function decimals() external view returns (uint8)
        function symbol() external view returns (string memory)
        function transfer(address recipient, uint256 amount) external returns (bool)
        function allowance(address owner, address spender) external view returns (uint256)
        function approve(address spender, uint256 amount) external returns (bool)
        function transferFrom( address sender, address recipient, uint256 amount) external returns (bool)
        event Transfer(address indexed from, address indexed to, uint256 value)
        event Approval(address indexed owner, address indexed spender, uint256 value)
    ]"#,
    event_derives(serde::Deserialize, serde::Serialize)
);

#[cfg(test)]
pub mod test_util {
    use std::{path::PathBuf, sync::Arc};

    use anyhow::Result;
    use ethers::{
        contract::ContractFactory,
        middleware::SignerMiddleware,
        providers::{Http, Provider},
        signers::{LocalWallet, Signer},
        solc::{Artifact, Project, ProjectPathsConfig},
    };

    use crate::{
        async_runtime as rt,
        protocols::eth::{
            AnvilRpcManager, ChainId, ChecksumAddress, RpcManagerI, RpcProvider,
        },
    };

    pub struct TestContractDeployer {
        pub chain_id: ChainId,
        pub anvil_rpc: AnvilRpcManager,
        pub rpc_provider: RpcProvider,
    }

    impl TestContractDeployer {
        pub fn init(chain_id: ChainId) -> Self {
            let anvil_rpc = AnvilRpcManager::new();
            let rpc_provider = anvil_rpc.eth_api_provider(chain_id);
            Self {
                chain_id,
                anvil_rpc,
                rpc_provider,
            }
        }

        /// Deployer wallet gets the initial balance of tokens.
        pub fn deployer_wallet(&self) -> LocalWallet {
            let wallet = self.anvil_rpc.wallet();
            wallet.with_chain_id(self.chain_id)
        }

        pub fn provider(&self) -> Provider<Http> {
            self.rpc_provider.provider.clone()
        }

        /// Deploy FungibleTokenTest ERC20 contract on local Anvil node.
        /// Returns the contract address.
        /// Based on https://github.com/gakonst/ethers-rs/blob/69f24e03efca769ed2acc96b95029b3f07fd5493/examples/contract_human_readable.rs
        pub async fn deploy_fungible_token_test_contract_async(
            &self,
        ) -> Result<ChecksumAddress> {
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

            // Deploy FungibleTokenTest contract
            let wallet = self.deployer_wallet();
            let client = SignerMiddleware::new(self.provider(), wallet);
            let client = Arc::new(client);
            let factory =
                ContractFactory::new(abi.unwrap(), bytecode.unwrap(), client.clone());
            let contract = factory.deploy(())?.send().await?;

            Ok(contract.address().into())
        }

        pub fn deploy_fungible_token_test_contract(&self) -> Result<ChecksumAddress> {
            rt::block_on(self.deploy_fungible_token_test_contract_async())
        }
    }
}
