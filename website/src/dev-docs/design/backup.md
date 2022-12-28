# Cloud Backup

This document contains an overview of cloud backup options on iOS and our chosen
solution, the [SealVault iCloud Backup.](#sealvault-icloud-backup)

## iCloud Device Backup

When a user
[enables](https://support.apple.com/en-gb/guide/iphone/iph3ecf67d29/ios) iCloud
backups for their device, their local keychain and app data gets backed up as
part of that. However, items stored on the local keychain can be only restored
on the same device as their encryption key is tangled with the root key of the
device's hardware security module.[^0] 

The [SK-KEK](./data.md#secret-key-encryption-keys) is stored on the local
keychain, which means that SealVault users would be only able to restore
SealVault to full functionality from an iCloud device backup on the same device
where it was created. Reinstalling on the same device is not the intended use
case for iCloud device backups, and if we just supported that it would lead to
confusion, so we 
**[exclude](https://developer.apple.com/documentation/foundation/optimizing_your_app_s_data_for_icloud_backup)
the user's SealVault data from iCloud device backups.**

## iCloud Keychain

In order to support recovering from an iCloud device backup on other devices, we
could store the [SK-KEK](./data.md#secret-key-encryption-keys) on the iCloud
Keychain. 

The iCloud Keychain allows users to securely sync their passwords between Apple
devices. The iCloud Keychain and the recovery process (in case a user loses all
their devices) are designed to protect a user's passwords under the following
conditions:[^5]

> - A user’s iCloud account is compromised.
> - iCloud is compromised by an external attacker or employee.
> - A third party accesses user accounts.

In order to provide these guarantees for recovery, the iCloud Keychain relies on
the following mechanisms:[^7]

- The user's device passcode.
- A cloud hardware security module (HSM) with an embedded secure remote password
  protocol.
- Limiting the number of passcode tries to fetch the backup key from the HSM
  within the HSM.

We believe these controls are sufficient to protect passwords that are typically
used in conjunction with a second factor for sensitive accounts. However, for
blockchain secret keys, the key compromise by itself can have disastrous
effects, therefore the **iCloud Keychain security controls are insufficient for
Sealvault** due to a combination of the following factors:

- Device passcodes often have very low entropy, e.g. repeating the same number
  is a common device passcode.
- Users sometimes use the same 6-digit code across services which makes the
  device passcode susceptible to phishing or leakage through non-Apple services.
- New vulnerabilities are routinely founds in HSMs.[^8]
- Apple has a history of failing to properly enforce limit type security
  controls (to be fair other companies struggle with this as well).[^9]
- It's
  [unlikely](https://www.lawfareblog.com/apples-cloud-key-vault-exceptional-access-and-false-equivalences)
  that there is an undisclosed law enforcement backdoor in iCloud Keychain, but
  given that it's the highest value target globally, it shouldn't be discarded
  entirely that it exists or that it will be added in the future. And of course
  such a backdoor would greatly weaken defenses against crooks as well.
    

## SealVault iCloud Backup

When users enable iCloud backups in the SealVault app settings, they can recover
their [data](./data.md) if they lose access to their device or delete the
app.[^50] Once we support [syncing,](./sync.md) users will be able to recover
from other devices as well and iCloud backups will be only necessary to recover
in case all devices are lost.

SealVault stores cloud backups in app-specific iCloud storage in a folder for
backups. New backups are created when the app goes in the background. SealVault
keeps only the most recent backup in iCloud storage for each device.

!!! question "Why don't we store the active SQLite DB in iCloud Storage?"

    There are two reasons. The first is that SQLite database files shouldn't be
    opened from synced cloud storage as that may lead to data loss. The second is
    that if the user is logged out of iCloud, then the app would stop working.

### Backup Contents

The backup is a ZIP file that consists of a SQLite backup file encrypted on the
device and metadata about the backup in a JSON file.  The metadata is stored in
plaintext, but it's authenticated with our chosen [AEAD](./cryptography.md#aead)
construct.  The metadata consists of:

- backup scheme version,
- backup version on the device,
- device identifier,
- operating system of the device,
- timestamp when the backup was created,
- KDF nonce,
- encryption nonce.

The backup version is a monotonically increasing integer on each device. The
backup version may have gaps. Since the backup version is incremented every
time the user exits the app (when a new backup is created), the backup version
can reveal how much the user uses the app.

### Backup Password

The purpose of the backup password is to protect the backup if the user's iCloud
Storage and Keychain are compromised. The backup password should be easy to
write down on paper, but it should be strong enough that, if all other measures
fail, it's impossible to decrypt the backup without the backup password on
classical computers.

A 20 character long backup password using [Crockford's base32
alphabet](https://www.crockford.com/base32.html) is generated with the
[CSPRNG](./cryptography.md#csprng) on the device when backups are enabled by the
user. The backup password is stored on the local (device only) keychain. 

This is an example backup password: `8FD93-EYWZR-GB7HX-QAVNS`.

The backup password has 100-bit entropy, and it is autogenerated to ensure this
level of entropy. 100-bit entropy is a good balance between not being too
annoying to write down and having a wide margin of safety in case an unforeseen
vulnerability is discovered in the password-based [KDF.](./cryptography.md#kdfs)

#### Base32

The backup password uses the base32 alphabet instead of a word-based scheme that
would be easier to write down with integrity due to phishing concerns.
Blockchain users are conditioned to enter seed phrases into applications and if
a user confused a word-based backup password with a seed phrase, they could be
easily tricked into entering it in a malicious application. 

Among non-word-based encoding schemes, [Crockford's base32
alphabet](https://www.crockford.com/base32.html) finds the best balance between
being easy to write down with integrity while producing high entropy passwords
with relatively short length. When decoding the user input, we use Crockford's
[decoding scheme](https://www.crockford.com/base32.html) that doesn't
differentiate between upper and lower case and maps ambiguous characters that
are not part of the alphabet to their counterpart that is in the alphabet (e.g.
the letter O is mapped to the number 0).

#### Self-Custody Password Storage

The user is advised to write the backup password down on paper and store it in a
secure location, or if that's not feasible, to store it in a password manager
like 1Password or Bitwarden.

The user can view and copy the backup password any time in the application
settings on the device after biometric or passcode authentication in order to 

1. Let them store it securely at their convenience, instead of forcing them to
   confirm it when they enable the feature as it's unlikely that they are in a
   position to store it securely at that time.
1. Let them verify that the password that they stored is the correct backup
   password (especially important since we support [password
   rotation](#password-rotation)).

Viewing and copying the backup password opens up [side-channel
attacks](./attack-tree.md#backup-disclosure) on the password, but since the
password is just [one factor](./attack-tree.md#backup-disclosure) among the
backup defenses, we believe that the above considerations trump side-channel
concerns.

### KDF Secret

A 256-bit KDF secret (**KDF-S**) is generated on the device with the
[CSPRNG](./cryptography.md#csprng) and stored on the user's iCloud Keychain. The
KDF-S is transparent to the user.

The KDF-S serves as a defense-in-depth measure against lax treatment of the
backup password as iCloud Keychain items have stronger
[protection](https://support.apple.com/en-gb/HT202303) than iCloud Storage
items.  For example, if a user stores the backup password in the Notes app and
iCloud Storage is compromised (but not the iCloud Keychain), then the KDF-S
keeps the user safe.

### Backup Encryption Keys

There are two 256-bit backup encryption keys:

- The database backup encryption key (**DB-BK**).
- The secret key backup key (**SK-BK**) which can be used to decrypt
  [SK-DEK](./data.md#secret-key-encryption-keys) that is stored encrypted inside
  the database.

### Key Derivation Functions

[Argon2id](./cryptography.md#kdfs) is used to derive the root backup key
(**ROOT-BK**) from the [backup password](#backup-password) and the
[KDF-S](#kdf-secret). [BLAKE3](./cryptography.md#kdfs) is used to derive DB-BK
and SK-BK from the ROOT-BK with unique static context strings.

The backup password, the DB-BK and the SK-BK are stored in the local iOS
keychain (not iCloud Keychain). The backup password is stored so that we can
[display](#self-custody-password-storage) it to the user and derive other keys
in the future if necessary. The DB-BK and SK-BK are stored to avoid having to
recompute the expensive Argon2id function for every backup.

### Disabling Backups

Users may choose to disable backups any time.

When backups are disabled, the [backup password](#backup-password), the [DB-BK
and SK-BK](#backup-encryption-keys) are deleted from the local keychain. The
[KDF-S](#kdf-secret) is deleted from the iCloud Keychain. The backups created on
the device are also deleted from iCloud storage.

While the old backups are deleted from the application's perspective, we cannot
guarantee that all copies are deleted by the cloud storage provider. The KDF-S
serves as a defense in-depth measure here as well, since it's less likely that
both the deleted KDF-S and the corresponding deleted encrypted backup are
preserved than just the encrypted backup being preserved.

### Password Rotation

Users may choose to rotate their [backup password](#backup-password) any time by
disabling backups first then enabling again.

### Recovery

!!! info

    As noted [above](#icloud-device-backup), SealVault cannot be recovered from
    iCloud Device Backups. 

When installing the SealVault app on an iOS device, users may choose to recover
from the chronologically latest backup if there are any and they're logged in to
iCloud and iCloud Keychain is enabled.  

In order to recover, the user has to enter their [backup
password](#backup-password) via the device keyboard. Once recovered, backups
have to be enabled anew on the device and a new backup password will be
generated.

### Post-Quantum Security

It seems likely that quantum computers will be built in the future that can
brute force an N-bit key space of a symmetric encryption algorithm in
$O(2^{0.5N})$ time using [Grover's
algorithm.](https://en.wikipedia.org/wiki/Grover%27s_algorithm)  For this reason
it is recommended to switch from 128-bit to 256-bit symmetric encryption
algorithms to render such attacks unfeasible due to $2^{128}$ theoretical time
cost.[^10]

Our chosen [AEAD](./cryptography.md#aead) construct has 256-bit keys, but the
[backup password](#backup-password) has only 100-bit entropy.  Does this make
our cloud backups **vulnerable to quantum attacks?**

**We think not,** because in order to make use of Grover's algorithm, the target
function has to be implemented in a quantum circuit. Since the backup keys are
derived with KDFs, in order to attack backup passwords, the memory-hard
[Argon2id KDF,](./cryptography.md#kdfs) the [BLAKE3 KDF](./cryptography.md#kdfs)
and the [XChaCha20 cipher](./cryptography.md#aead) have to be implemented in a
single quantum circuit.[^20] If such a complex circuit can be designed at all,
it's unlikely that currently envisioned quantum computers would have the
capacity to execute it. And even if they do, it's unclear whether the
theoretical asymptotic speed up would result in more cost-efficient attacks than
those with classical computers due to a high constant factor.[^30]

#### What if We Are Wrong?

Long before attacking our 100-bit entropy backup passwords with Grover's
algorithm could become feasible, quantum computers running [Shor's
algorithm](https://en.wikipedia.org/wiki/Shor%27s_algorithm) would break
elliptic curve signatures used by all blockchains today.  This will necessitate
a blockchain keypair migration in SealVault.  At that point we will have a much
better understanding of quantum computers' capabilities and we can reassess our
choice of 100-bit entropy backup passwords and migrate to a stronger solution if
necessary.

This leaves open the possibility that,

1. if we are wrong in our current confidence about the post-quantum security
   provided by the Argon2, AND
2. an attacker with unexpected quantum capabilities gains access to legacy
   cloud backups that are somehow preserved in spite of deleting them,

some user's dapp usage metadata[^40] could become compromised decades from now.
We think this is an acceptable risk.

[^0]: 
    [Apple Platform Security Manual, May 2022](https://help.apple.com/pdf/security/en_GB/apple-platform-security-guide-b.pdf) p. 129.
[^5]:
    [Apple Platform Security Manual, May 2022](https://help.apple.com/pdf/security/en_GB/apple-platform-security-guide-b.pdf) p. 143.
[^7]:
    [Agost's Blog: iCloud Keychain Security, April 2022](https://blog.agostbiro.net/2022/04/icloud-keychain-security/)
[^8]:
    See [Anderson, Security Engineering, 3rd
    ed.](https://www.cl.cam.ac.uk/~rja14/book.html) Chapter 18.3 for a history of
    HSM attacks or [CryptoSense Blog: How Ledger Hacked an HSM, June
    2019](https://cryptosense.com/blog/how-ledger-hacked-an-hsm) for a recent high
    profile example.
[^9]:
    Public limit bypass vulnerabilities at Apple from the past decade:

    - 2014: [Apple ID password brute force throught Find my iPhone endpoint.](https://www.engadget.com/2014-09-01-find-my-iphone-exploit.html)
    - 2015: [Apple ID password brute force through iOS iCloud login endpoint](.https://www.theregister.com/2015/01/07/idict_icloud_hacking_tool_blunted/)
    - 2016: [iPhone 5c passcode retry counter bypass.](https://arxiv.org/abs/1609.04327)
    - 2020: [Forgot password endpoint rate limit bypass.](https://thezerohack.com/apple-vulnerability-bug-bounty) 
        (Apple acknowledged the vulnerability, but claimed that it couldn't lead to
        account takeover by itself.)
    - 2022: [T2 security chip retry limit bypass.](https://9to5mac.com/2022/02/17/t2-mac-security-vulnerability-passware/)
[^10]: 
    [Bernstein & Lange, 2017: Post-quantum cryptography.](https://eprint.iacr.org/2017/314.pdf)
[^20]: 
    A potential weakness of our choice of [KDFs](./cryptography.md#kdfs) and
    [AEAD](./cryptography.md#aead) is that they're all built on the ChaCha
    permutation, and it's possible that this could be exploited in the design of a
    quantum circuit targeting our backup scheme. We've considered switching one of
    the components to a construct that isn't built on the ChaCha permutation, but
    decided against it as any cleverness in this regard is more likely to introduce
    vulnerabilities than solve the extremely unlikely and [low
    impact](#what-if-we-are-wrong) quantum problem.
[^30]: 
    [Aumasson, 2019: Too Much Crypto.](https://eprint.iacr.org/2019/1492.pdf)
[^40]:
    Remember, the blockchain key pairs would be long broken at this point by 
    Shor's algorithm.  See what we store in the [data section.](./data.md)

[^50]:
    Implementation is [WIP.](https://github.com/sealvault/sealvault/issues/32)