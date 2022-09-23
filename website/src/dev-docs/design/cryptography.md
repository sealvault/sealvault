# Cryptography

## CSPRNG

Rust's
[rand::rngs::ThreadRng](https://docs.rs/rand/latest/rand/rngs/struct.ThreadRng.html)
is used to generate cryptographically secure random bytes.  This
[uses](https://docs.rs/getrandom/latest/getrandom/#supported-targets)
[SecRandomCopyBytes](https://developer.apple.com/documentation/security/1399291-secrandomcopybytes?language=objc)
as the entropy source on iOS.


## AEAD

We need an authenticated encryption with associated data (AEAD) construct to
encrypt [cloud backups](./data.md#cloud-backup) on the device and authenticate
backup metadata.  We need an authenticated encryption construct to encrypt
private keys in [device storage.](./data.md#device-storage) For simplicity,
we'll use an AEAD for both cases.

We need the AEAD to have an audited, cross-platform Rust implementation.  We
choose a 256-bit key size to provide 128-bit post-quantum security level.
Compliance to a particular standard is not a goal in the choice of AEAD
constructs.

The [RustCrypto AEADs](https://github.com/RustCrypto/AEADs) library offers two
fully audited and one partially audited AEAD construct:

* [AEAS-GCM-SIV](https://github.com/RustCrypto/AEADs/tree/master/aes-gcm-siv)
(partially audited)
* [AES-GCM](https://github.com/RustCrypto/AEADs/tree/master/aes-gcm)
(fully audited)
* [XChaCha20Poly1305](https://github.com/RustCrypto/AEADs/tree/master/chacha20poly1305)
(fully audited)

We choose **XChaCha20Poly1305** for our AEAD construct for the following reasons:

1. It's recommended by the [IRTF](https://datatracker.ietf.org/doc/html/rfc7539)[^0] 
and it's fully
[audited.](https://research.nccgroup.com/2020/02/26/public-report-rustcrypto-aes-gcm-and-chacha20poly1305-implementation-review/)
2. It supports 192-bit nonces which means we can ensure nonce uniqueness without
coordination by picking nonces at random.
3. Its simple design makes it easier to use and audit than the AES constructs.

Encryption keys and nonces are generated with the [CSPRNG.](#csprng) See the
[data](./data.md#solution) section to see how encryption keys are stored.

## Elliptic-Curve Cryptography

### ECDSA-secp256k1 for Ethereum

We use the [RustCrypto
secp256k1](https://github.com/RustCrypto/elliptic-curves/tree/master/k256) crate
for Ethereum protocol signatures. This is a constant time pure Rust
implementation by reputable authors that is popular in the Rust Ethereum
ecosystem, but it has not been audited independently.

[^0]: 
    The [linked RFC](https://datatracker.ietf.org/doc/html/rfc7539) is actually
    about ChaCha20Poly1305, not XChaCha20Poly1305.  The difference is that
    XChaCha20Poly1305 supports 192-bit nonces which make it possible to avoid nonce
    reuse simply by picking them at random.

