// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// Based on: https://github.com/gakonst/ethers-rs/blob/239f559ca04b296a1b4cd1fc7588f29b125be565/ethers-middleware/src/signer.rs
use std::{convert::From, fmt};

use async_trait::async_trait;
use ethers::{
    core::types::{
        transaction::{eip2718::TypedTransaction, eip2930::AccessListWithGasUsed},
        Address, BlockId, Bytes, Signature as EthereumSignature, U256, U64,
    },
    providers::{
        maybe, Http, Middleware, MiddlewareError, PendingTransaction, Provider,
        ProviderError,
    },
};
use k256::{FieldBytes, Secp256k1};
use sha3::{Digest, Keccak256};

use crate::{
    protocols::eth::{chain_id::ChainId, signing_key::SigningKey, EthereumAsymmetricKey},
    signatures::RecoverableSignature,
    Error,
};

pub struct Signer<'a> {
    signing_key: &'a SigningKey,
}

impl<'a> Signer<'a> {
    pub fn new(signing_key: &'a SigningKey) -> Self {
        Self { signing_key }
    }

    /// The signing key's address.
    fn address(&self) -> Address {
        self.signing_key.address.to_address()
    }

    /// The addresses chain id.
    fn chain_id(&self) -> ChainId {
        self.signing_key.chain_id
    }

    /// The signing key.
    fn key(&self) -> &EthereumAsymmetricKey {
        &self.signing_key.key
    }

    /// Make sure transaction parameters match our address data.
    fn verify_tx_params(&self, tx: &TypedTransaction) -> Result<(), Error> {
        if tx.from() != Some(&self.address()) {
            return Err(Error::Fatal {
                error: "Wrong from in tx params".into(),
            });
        }

        if tx.chain_id() != Some(self.chain_id().into()) {
            return Err(Error::Fatal {
                error: "Wrong chain id in tx params".into(),
            });
        }

        Ok(())
    }

    /// UNSAFE: As it operates on opaque bytes, this method is unsafe to use unless the caller
    /// ensures that it's used on correctly preprocessed data.
    fn hazmat_sign_bytes<T: AsRef<[u8]>>(
        &self,
        data: T,
    ) -> Result<EcdsaEthereumSignature, Error> {
        let digest = Keccak256::new_with_prefix(data.as_ref());

        let sig = self.key().try_sign_digest(digest)?;

        Ok(EcdsaEthereumSignature::new(&sig, self.chain_id()))
    }

    /// Perform an ECDSA signature on an Ethereum transaction using the Secp256k1 curve with
    /// RFC6979 deterministic `k` value.
    fn sign_tx(&self, tx: &TypedTransaction) -> Result<EcdsaEthereumSignature, Error> {
        self.verify_tx_params(tx)?;

        let encoded_tx = tx.rlp();
        self.hazmat_sign_bytes(encoded_tx)
    }

    /// Perform EIP155 signature.
    fn sign_for_on_chain(
        &self,
        tx: &TypedTransaction,
    ) -> Result<EIP155EthereumSignature, Error> {
        Ok(self.sign_tx(tx)?.into())
    }

    const PERSONAL_SIGN_PREFIX: &'static str = "\x19Ethereum Signed Message:\n";

    fn personal_sign_message<T: AsRef<[u8]>>(data: T) -> Vec<u8> {
        let data = data.as_ref();
        let mut message =
            format!("{}{}", Self::PERSONAL_SIGN_PREFIX, data.len()).into_bytes();
        message.extend_from_slice(data);
        message
    }

    /// Perform off-chain Ethereum signature according to `personal_sign` standard:
    /// https://geth.ethereum.org/docs/rpc/ns-personal#personal_sign
    pub fn personal_sign<T: AsRef<[u8]>>(
        &self,
        data: T,
    ) -> Result<OffChainEthereumSignature, Error> {
        let message = Self::personal_sign_message(data);
        Ok(self.hazmat_sign_bytes(message)?.into())
    }
}

/// Signer middleware for ethers-rs using our key management.
pub(super) struct SignerMiddleware<'a> {
    provider: &'a Provider<Http>,
    signer: Signer<'a>,
}

impl<'a> SignerMiddleware<'a> {
    pub fn new(provider: &'a Provider<Http>, signing_key: &'a SigningKey) -> Self {
        let signer = Signer::new(signing_key);
        Self { provider, signer }
    }
}

#[async_trait]
impl<'a> Middleware for SignerMiddleware<'a> {
    type Error = SignerMiddlewareError<Provider<Http>>;
    type Provider = Http;
    type Inner = Provider<Http>;

    fn inner(&self) -> &Self::Inner {
        self.provider
    }

    /// Returns the client's address
    fn default_sender(&self) -> Option<Address> {
        Some(self.signer.address())
    }

    async fn fill_transaction(
        &self,
        tx: &mut TypedTransaction,
        block: Option<BlockId>,
    ) -> Result<(), Self::Error> {
        if tx.from().is_none() {
            tx.set_from(self.signer.address());
        }

        if tx.chain_id().is_none() {
            let chain_id: U64 = self.signer.chain_id().into();
            tx.set_chain_id(chain_id);
        }

        let nonce = maybe(
            tx.nonce().cloned(),
            self.get_transaction_count(self.signer.address(), block),
        )
        .await?;
        tx.set_nonce(nonce);

        self.inner().fill_transaction(tx, block).await?;

        Ok(())
    }

    /// Signs and broadcasts the transaction. The optional parameter `block` can be passed so that
    /// gas cost and nonce calculations take it into account. For simple transactions this can be
    /// left to `None`.
    async fn send_transaction<T: Into<TypedTransaction> + Send + Sync>(
        &self,
        tx: T,
        block: Option<BlockId>,
    ) -> Result<PendingTransaction<'_, Self::Provider>, Self::Error> {
        let mut tx = tx.into();

        // fill any missing fields
        self.fill_transaction(&mut tx, block).await?;

        let sig: EthereumSignature = self.signer.sign_for_on_chain(&tx)?.into();
        let signed_tx = tx.rlp_signed(&sig);

        // Submit the raw transaction
        let res = self.inner().send_raw_transaction(signed_tx).await?;

        Ok(res)
    }

    async fn estimate_gas(
        &self,
        tx: &TypedTransaction,
        block: Option<BlockId>,
    ) -> Result<U256, Self::Error> {
        self.signer.verify_tx_params(tx)?;
        let res = self.inner().estimate_gas(tx, block).await?;
        Ok(res)
    }

    async fn call(
        &self,
        tx: &TypedTransaction,
        block: Option<BlockId>,
    ) -> Result<Bytes, Self::Error> {
        // Call doesn't mutate, no need to verify params.
        let res = self.inner().call(tx, block).await?;
        Ok(res)
    }

    async fn get_chainid(&self) -> Result<U256, Self::Error> {
        Ok(self.signer.chain_id().into())
    }

    async fn is_signer(&self) -> bool {
        true
    }

    async fn sign<T: Into<Bytes> + Send + Sync>(
        &self,
        _: T,
        _: &Address,
    ) -> Result<EthereumSignature, Self::Error> {
        unimplemented!("eth_sign is unsafe and not supported");
    }

    async fn sign_transaction(
        &self,
        tx: &TypedTransaction,
        _: Address,
    ) -> Result<EthereumSignature, Self::Error> {
        Ok(self.signer.sign_for_on_chain(tx)?.into())
    }

    async fn create_access_list(
        &self,
        tx: &TypedTransaction,
        block: Option<BlockId>,
    ) -> Result<AccessListWithGasUsed, Self::Error> {
        self.signer.verify_tx_params(tx)?;
        let res = self.inner().create_access_list(tx, block).await?;
        Ok(res)
    }
}

impl<'a> fmt::Debug for Signer<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Signer")
            .field("signing_key", &self.signing_key)
            .finish()
    }
}

impl<'a> fmt::Debug for SignerMiddleware<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SignerMiddleware")
            .field("signer", &self.signer)
            .finish()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SignerMiddlewareError<M: Middleware> {
    /// Thrown when the internal middleware errors
    #[error(transparent)]
    Middleware(M::Error),
    #[error(transparent)]
    Provider(#[from] ProviderError),
    #[error(transparent)]
    App(#[from] Error),
}

impl<M: Middleware> MiddlewareError for SignerMiddlewareError<M> {
    type Inner = M::Error;

    fn from_err(src: M::Error) -> Self {
        SignerMiddlewareError::Middleware(src)
    }

    fn as_inner(&self) -> Option<&Self::Inner> {
        match self {
            SignerMiddlewareError::Middleware(e) => Some(e),
            _ => None,
        }
    }
}

impl<M: Middleware> From<SignerMiddlewareError<M>> for Error {
    fn from(error: SignerMiddlewareError<M>) -> Self {
        match error {
            SignerMiddlewareError::Middleware(middleware_error) => {
                match middleware_error.as_provider_error() {
                    Some(provider_error) => provider_error.into(),
                    None => Error::Retriable {
                        error: middleware_error.to_string(),
                    },
                }
            }
            SignerMiddlewareError::Provider(provider_error) => provider_error.into(),
            SignerMiddlewareError::App(inner) => inner,
        }
    }
}

/// An `EthereumSignature` where `v` is in [0, 3].
struct EcdsaEthereumSignature {
    sig: EthereumSignature,
    chain_id: ChainId,
}

impl EcdsaEthereumSignature {
    fn new(recoverable_sig: &RecoverableSignature<Secp256k1>, chain_id: ChainId) -> Self {
        let v = u8::from(recoverable_sig.recovery_id) as u64;

        let r_bytes: FieldBytes = recoverable_sig.signature.r().into();
        let r = U256::from_big_endian(r_bytes.as_slice());
        let s_bytes: FieldBytes = recoverable_sig.signature.s().into();
        let s = U256::from_big_endian(s_bytes.as_slice());

        let sig = EthereumSignature { r, s, v };

        Self { sig, chain_id }
    }
}

/// An `EthereumSignature` where `v` is in [27, 30] (assumes uncompressed public key).
pub struct OffChainEthereumSignature {
    inner: EthereumSignature,
}

impl fmt::Display for OffChainEthereumSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{}", self.inner)
    }
}

impl From<EcdsaEthereumSignature> for OffChainEthereumSignature {
    fn from(mut sig: EcdsaEthereumSignature) -> Self {
        sig.sig.v += 27;
        Self { inner: sig.sig }
    }
}

/// An `EthereumSignature` where `v` is computed according to EIP155 for cross-chain replay
/// attack protection.
struct EIP155EthereumSignature {
    inner: EthereumSignature,
}

impl From<EcdsaEthereumSignature> for EIP155EthereumSignature {
    fn from(mut sig: EcdsaEthereumSignature) -> Self {
        let chain_id: u64 = sig.chain_id.into();
        sig.sig.v += 35 + chain_id * 2;
        Self { inner: sig.sig }
    }
}

// We only implement from `EIP155EthereumSignature` for `EthereumSignature` so that the other
// unsafe/incorrect variants aren't converted accidentally.
impl From<EIP155EthereumSignature> for EthereumSignature {
    fn from(sig: EIP155EthereumSignature) -> Self {
        sig.inner
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use anyhow::Result;
    use ethers::core::{
        types::{RecoveryMessage, TransactionRequest},
        utils::{hex, keccak256},
    };
    use lazy_static::lazy_static;

    use super::*;

    struct PersonalSignTest {
        address: &'static str,
        private_key: &'static str,
        data: &'static str,
        signature: &'static str,
    }

    impl PersonalSignTest {
        fn key(&self) -> EthereumAsymmetricKey {
            let private_key = self.private_key.strip_prefix("0x").expect("0x prefix");
            let key = private_key
                .parse::<EthereumAsymmetricKey>()
                .expect("valid private key");
            key
        }

        fn message(&self) -> Bytes {
            self.data.as_bytes().to_vec().into()
        }
    }

    lazy_static! {
        // Test vectors from: https://github.com/ChainSafe/web3.js/blob/8620cba19f2a9250d395e0717669b274a89521a5/test/eth.accounts.sign.js#L7
        static ref PERSONAL_SIGN_VECTORS: Vec<PersonalSignTest> = vec![
            PersonalSignTest {
                address: "0xEB014f8c8B418Db6b45774c326A0E64C78914dC0",
                private_key: "0xbe6383dad004f233317e46ddb46ad31b16064d14447a95cc1d8c8d4bc61c3728",
                data: "Some data",
                // signature done with personal_sign
                signature: "0xa8037a6116c176a25e6fc224947fde9e79a2deaa0dd8b67b366fbdfdbffc01f953e41351267b20d4a89ebfe9c8f03c04de9b345add4a52f15bd026b63c8fb1501b"
            },
            PersonalSignTest {
                address: "0xEB014f8c8B418Db6b45774c326A0E64C78914dC0",
                private_key: "0xbe6383dad004f233317e46ddb46ad31b16064d14447a95cc1d8c8d4bc61c3728",
                data: "Some data!%$$%&@*",
                // signature done with personal_sign
                signature: "0x05252412b097c5d080c994d1ea12abcee6f1cae23feb225517a0b691a66e12866b3f54292f9cfef98f390670b4d010fc4af7fcd46e41d72870602c117b14921c1c"
            }
        ];
    }

    #[test]
    fn signature_matches_ethers_rs_signer() -> Result<()> {
        const TO_ADDRESS: &str = "F0109fC8DF283027b6285cc889F5aA624EaC1F55";
        const SK: &str =
            "4c0883a69102937d6231471b5dbb6204fe5129617082792ae468d01a3f362318";
        const SIG_HASH: &str =
            "de8db924885b0803d2edc335f745b2b8750c8848744905684c20b987443a9593";
        const RLP: &str = "f869808504e3b29200831e848094f0109fc8df283027b6285cc889f5aa624eac1f55843b\
        9aca008025a0c9cf86333bcb065d140032ecaab5d9281bde80f21b9687b3e94161de42d51895a0727a108a0b8d1\
        01465414033c3f705a9c7b826e596766046ee1183dbc8aeaa68";

        let chain_id = ChainId::EthMainnet;

        // Retrieved test vector from:
        // https://web3js.readthedocs.io/en/v1.2.0/web3-eth-accounts.html#eth-accounts-signtransaction
        let tx: TypedTransaction = TransactionRequest {
            from: None,
            to: Some(TO_ADDRESS.parse::<Address>().unwrap().into()),
            value: Some(1_000_000_000.into()),
            gas: Some(2_000_000.into()),
            nonce: Some(0.into()),
            gas_price: Some(21_000_000_000u128.into()),
            data: None,
            // Difference from original test vector: chain id is added extra here, because ethers-rs
            // sets it before signing.
            chain_id: Some(chain_id.into()),
        }
        .into();

        assert!(matches!(tx, TypedTransaction::Legacy(_)));

        let key = SK.parse::<EthereumAsymmetricKey>()?;
        let signing_key = SigningKey::new(key, chain_id)?;
        let signer = Signer::new(&signing_key);

        // We're calling implementation specific `hazmat_sign_bytes` here instead of the middleware
        // `sign_transaction`, because our implementation of `sign_transaction` refuses to sign a
        // transaction if `from` is unset, but `from` is None in the test vector.
        let message: Vec<u8> = tx.rlp().to_vec();
        let sig: EIP155EthereumSignature = signer.hazmat_sign_bytes(&message)?.into();
        let sig: EthereumSignature = sig.into();
        let hash = keccak256(&message);
        sig.verify(hash, signing_key.address)?;
        let sig_bytes = tx.rlp_signed(&sig);

        assert_eq!(keccak256(&sig_bytes)[..], hex::decode(SIG_HASH).unwrap());
        let expected_rlp = Bytes::from(hex::decode(RLP).unwrap());
        assert_eq!(sig_bytes, expected_rlp);

        Ok(())
    }

    #[test]
    fn personal_sign_message() -> Result<()> {
        let message = Signer::personal_sign_message("Some message");
        let message = String::from_utf8(message)?;
        assert!(message.starts_with("\x19Ethereum Signed Message:\n"));
        Ok(())
    }

    #[test]
    fn personal_sign() -> Result<()> {
        let chain_id = ChainId::default_dapp_chain();
        for case in PERSONAL_SIGN_VECTORS.iter() {
            let signing_key = SigningKey::new(case.key(), chain_id)?;
            assert_eq!(signing_key.address.to_string(), case.address);

            let signer = Signer::new(&signing_key);

            let signature = signer.personal_sign(case.message())?;

            signature.inner.verify(
                keccak256(Signer::personal_sign_message(case.message())),
                signing_key.address,
            )?;

            let expected_signature: ethers::core::types::Signature =
                FromStr::from_str(case.signature)?;
            assert_eq!(signature.inner, expected_signature);

            assert!(signature.to_string().starts_with("0x"));
        }
        Ok(())
    }
}
