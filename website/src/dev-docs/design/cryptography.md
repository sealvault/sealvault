# Cryptography

This document contains the cryptographic primitives used by the SealVault
application, their parameters if any, and the rationale for their choice.

## CSPRNG

Rust's
[rand::rngs::ThreadRng](https://docs.rs/rand/latest/rand/rngs/struct.ThreadRng.html)
is used to generate cryptographically secure random bytes.  This
[uses](https://docs.rs/getrandom/latest/getrandom/#supported-targets)
[SecRandomCopyBytes](https://developer.apple.com/documentation/security/1399291-secrandomcopybytes?language=objc)
as the entropy source on iOS.

## KDFs

We need a memory-hard password-based key derivation function to produce a [root
backup key](./backup.md#key-derivation-functions) from the [backup
password.](./backup.md#backup-password)  We need an additional cheap to compute
key-derivation function to derive [context-specific
keys](./backup.md#backup-encryption-keys) from the root backup key.

We need the KDFs to have cross-platform Rust implementations. We'd prefer the
KDFs to have audited Rust implementations, but there aren't any. Compliance to a
particular standard is not a goal in the choice of KDF constructs.

### Argon2id

Our options for a memory-hard password-based key derivation function are:

- [Argon2id](https://en.wikipedia.org/wiki/Argon2)
- [Scrypt](https://en.wikipedia.org/wiki/Scrypt)

We choose Argon2id by
[RustCrypto](https://github.com/RustCrypto/password-hashes/tree/master/argon2)
due to [OWASP
recommendation.](https://cheatsheetseries.owasp.org/cheatsheets/Password_Storage_Cheat_Sheet.html)

When picking Argon2id parameters, we must be careful not to trigger iOS memory
safeguards[^10] and not to drain the user's battery or heat the device
noticeably.  Therefore, we choose a memory size of 64MiB, iteration count of 10
and a parallelism count of 1.[^20] This will produce hashes in 500-600ms on
modern iPhones.

For the rest of the parameters, we use 128-bit salt length and 256-bit
[secret](./backup.md#kdf-secret) and tag length. Salts and secrets are generated
with the [CSPRNG.](#csprng)

### BLAKE3

We choose the [official BLAKE3 Rust
implementation](https://github.com/BLAKE3-team/BLAKE3) to produce additional
context specific keys from the root backup key for the following reasons:

1. It's a secure KDF that supports binding keys to contexts, and it has an
   official Rust implementation with an ergonomic interface that is compatible
   with RustCrypto traits.
2. We already use the BLAKE3 hash function for [deterministic
   ids.](./sync.md#deterministic-ids)

The alternative to BLAKE3 would be [HKDF](https://en.wikipedia.org/wiki/HKDF),
but it has an awkward interface for applications that already have a
cryptographically secure pseudorandom key (and thus don't need its extract
phase), and it can cause subtle problems in applications that use standalone
HMAC for other purposes (which we will possibly do in the future).


## AEAD

We need an authenticated encryption with associated data (AEAD) construct to
encrypt [cloud backups](./data.md#cloud-backup) on the device and authenticate
backup metadata.  We need an authenticated encryption construct to encrypt
secret keys of asymmetric keys in [device storage.](./data.md#device-storage)
For simplicity, we'll use an AEAD for both cases.

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

Nonces are generated with the [CSPRNG.](#csprng) Encryption keys are either
generated with the [CSPRNG](#csprng) or derived with the [KDFs.](#kdfs) See the
[data](./data.md#solution) section to see how encryption keys are stored.

## Elliptic-Curve Cryptography

### ECDSA-secp256k1 for Ethereum

We use the [RustCrypto
secp256k1](https://github.com/RustCrypto/elliptic-curves/tree/master/k256) crate
for Ethereum protocol signatures. This is a constant time pure Rust
implementation by reputable authors that is popular in the Rust Ethereum
ecosystem, but it has not been audited independently.

The alternative would be the [Rust
wrapper](https://docs.rs/secp256k1/latest/secp256k1/) around Bitcoin core's C
[libsecp256k1](https://github.com/bitcoin-core/secp256k1) which is the most
battle tested `secp256k1` implementation. In spite of this we went the
RustCrypto implementation for the following reasons:

1. We already have RustCrypto dependencies, we like the project, and we will be
   using more of their ECC crates in the future as they simplify our
   implementation with common traits.
1. We prefer pure Rust dependencies when possible for safety.

[^0]: 
    The [linked RFC](https://datatracker.ietf.org/doc/html/rfc7539) is actually
    about ChaCha20Poly1305, not XChaCha20Poly1305.  The difference is that
    XChaCha20Poly1305 supports 192-bit nonces which make it possible to avoid nonce
    reuse simply by picking them at random.

[^10]: 
    iOS might kill a process after a large memory spike if there is memory
    pressure on the device.

[^20]: 
    We keep the parallelism count at 1 to avoid potential cross-platform
    issues later from threading.

