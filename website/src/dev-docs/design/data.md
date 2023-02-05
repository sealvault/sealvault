# Data

SealVault stores the following data on the user's device:

* Data and key encryption keys.
* Asymmetric keys for digital signatures.
* Blockchain addresses derived from public keys of the user.
* Profiles and profile images.
* Metadata about dapps that the user has interacted with, e.g.:
    * Smart contract addresses,
    * URLs.
* Blockchain and dapp specific user settings.
* Timestamps for user actions.

SealVault doesn't store any data remotely.

SealVault sends crash reports to [Sentry.](https://docs.sentry.io/) Secrets are
never sent to Sentry. This is enforced by Rust's type system at compile time due
to lack of or opaque `Debug` and `Display` trait implementations for secret
values. For other user data, we do our best to prevent leaking personally
identifiable information into crash reports by carefully considering what is 
included in error messages and what is logged.

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

#### Secret-Key-Encryption-Keys

We store secret keys fo digital signatures (SKs) in the SQLite database
encrypted with our chosen [AEAD](./cryptography.md#aead) construct. The SK
data-encryption-key (SK-DEK) is also stored in the database with envelope
encryption wrapped by the key-encryption-key for SKs (SK-KEK).  The SK-KEK is
stored on the user's local (device only) iOS Keychain with the [“When
Unlocked”](https://support.apple.com/en-gb/guide/security/secb0694df1a/1/web/1)
data protection class.  This means that **SKs can be only decrypted when the
device is unlocked by the user.**

This layered encryption approach lets us decrypt SKs only when they're needed to
sign a transaction and wipe them from memory immediately after while letting us
perform other tasks like backups in the background when the device is locked.
Finally, storing all data (including SKs) in a single SQLite database makes it
easy to create backups with integrity and the same approach can be used on other
platforms as well.

[^1]:
    While we focus on the iOS platform initially, we want to be able to use
    the same storage solution when we expand to other platforms.


