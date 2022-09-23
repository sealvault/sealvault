# Data

SealVault stores the following data on the user's device:

* Data and key encryption keys
* Asymmetric keys for digital signatures
* Blockchain addresses derived from public keys of the user
* Metadata about dapps that the user has interacted with, eg.:
    * Smart contract addresses
    * URLs
* Blockchain and dapp specific user settings
* Timestamps for user actions

SealVault doesn't store any data remotely.

SealVault sends crash reports to [Sentry.](https://docs.sentry.io/) Secrets are
never sent to Sentry. This is enforced by Rust's type system at compile time due
to lack of or opaque `Debug` and `Display` trait implementations for secret
values. For other user data, we do our best to prevent leaking personally
identifiable information into crash reports.

## Device Storage

### Requirements
1. Encryption on disk.
2. Minimize potential key exposure window and allow wiping keys from memory.
3. Allows performing tasks that don't need keys in the background.
4. Easy to back up.
5. Cross-platform.[^1]

### Solution

We store data on the user's device in a SQLite database file encrypted by [iOS
Data
Protection](https://developer.apple.com/documentation/uikit/protecting_the_user_s_privacy/encrypting_your_app_s_files)
with the [“Protected Until First User
Authentication”](https://support.apple.com/en-gb/guide/security/secb010e978a/1/web/1)
class.  This means that data is always encrypted on disk, but the decryption key
for the database file is stored in memory after the user has unlocked the device
for the first time after boot.  Older iOS devices use 128-bit keys while newer
devices use 256-bit keys for file encryption with AES-XTS.

We store secret keys fo digital signatures (SKs) in the SQLite database
encrypted with our chosen AEAD construct. The SK data encryption key (SK-DEK) is
also stored in the database with envelope encryption wrapped by the key
encryption key for SKs (SK-KEK).  The SK-KEK is stored on the user's local
(device only) iOS Keychain with the [“When
Unlocked”](https://support.apple.com/en-gb/guide/security/secb0694df1a/1/web/1)
data protection class.  This means that SKs can be only decrypted when the
device is unlocked by the user.  

This layered encryption approach lets us decrypt SKs only when they're needed to
sign a transaction and wipe them from memory immediately after while letting us
perform other tasks like backups in the background when the device is locked.
Finally, storing all data (including SKs) in a single SQLite database makes it
easy to create backups with integrity and the same approach can be used on other
platforms as well.

### Deterministic IDs

We use deterministic IDs as primary keys for synced database entities, because
deterministic IDs make it easier to maintain referential integrity when syncing.

The deterministic ID is derived by producing a
[BLAKE3](https://github.com/BLAKE3-team/BLAKE3) hash of the namespaced entity
name and the unique fields of the entity with a 256-bit tag. The deterministic
id is used as a basis for security-decisions, so it's critical that adversaries
cannot create collisions.

The 256-bit tag is an extremely conservative parameter, because syncing is done
among one user's devices, and we can assume with a large margin of error that no
user will have more than $2^{24}$ items in a synced table since these items
are typically created on first user interaction with a dapp. This means that
there is an approx. $2^{-209}$ probability of collision for ids in each
table, which is negligible with an extremely large margin of error, and is safe
even against adversaries with unexpected quantum-computing capabilities. On the
other hand, picking a shorter tag wouldn't bring any real benefits, as by
halving the tag size, we could maybe save a megabyte of storage for power users,
and it wouldn't speed up DB queries in any meaningful way.

Due to our usage of deterministic IDs, we treat unique columns as immutable,
i.e. if a unique column needs to be changed, a new entity is created. DB
entities that have deterministic ids may only have a single unique constraint on
the table other than the primary key. This unique constraint may not span
nullable columns, as null values are treated as not-equal by SQL which goes
against the purpose of deterministic ids.

When receiving an empty value for one of the unique values, the deterministic id
implementation hashes a special marker value in place of the empty value in 
order to distinguish between `["", "foo"]`  and `["foo", ""]` and between unique 
values of differing lengths (the latter could be handled by including the length 
in the hash as well). The marker value is a random 256-bit value hard-coded into 
the implementation. The implementation returns an error if it receives the 
marker value as one of the unique values in order to prevent adversarial attacks
simulating an empty value.

The tag bytes are stored as a base32-encoded (no padding) string in the DB to 
help with debugging.

## Sync

Syncing data between a user's devices is planned for future releases.

## Cloud Backup

Cloud backups are planned for future releases to recover data if the user has
lost access to all devices.

[^1]:
    While we focus on the iOS platform initially, we want to be able to use
    the same storage solution when we expand to other platforms.


