# Fraudulent Transaction Attack Tree

We present an attack tree for [fraudulent blockchain client
transactions](./security-model.md) and our measures to mitigate the threats. The
attack tree is broken into its components for legibility.

```mermaid
flowchart BT
  sk_disclosure[Secret Key Disclosure]
  --> fraudulent_tx

  social_engineer[Social Engineering]
  --> sk_disclosure

  device_disclosure[Device Key Disclosure]
  --> sk_disclosure

  backup_disclosure[Backup Disclosure]
  --> sk_disclosure

  approval_spoofing[Approval Spoofing]
  --> fraudulent_tx[Fraudulent Tx]

  phishing[Phishing]
  --> approval_spoofing[Approval Spoofing]

  social_engineering[Social Engineering]
  --> approval_spoofing

  compromised_dapp[Compromised Dapp]
  --> approval_spoofing
```

There are two causes of fraudulent transactions:

1. **Secret key disclosure:** the attacker learns the user's secret key and can
produce arbitrary transactions. The attacker may learn the user's secret key
from the user, from the device or from a backup.  
2. **Approval spoofing:** the user authorizes a transaction with different
parameters than they intended to or the user performs an action which leads to
authorizing a transaction without being aware of authorizing a transaction.
Approval spoofing may happen through deception attacks or through a compromised
dapp.

---

## Secret Key Disclosure

### Social Engineering

An attacker may trick the user to share their secret key with them.  We prevent
these attacks by never letting the user view or copy secret keys.[^0]

### Device Key Disclosure

The attacker learns the secret key from the user's device.

```mermaid
flowchart BT

  privilege_escalation[/Privilege Escalation\]
  --> device_disclosure[Device Key Disclosure]

  os_vuln[OS Vulnerability]
  --> privilege_escalation

  malware[Malware on Device]
  --> privilege_escalation

  security_misconfiguration[/Security Misconfiguration\]
  --> device_disclosure

  malware
  --> security_misconfiguration

  bug[Bug]
  --> security_misconfiguration

  malicious_app[Malicious App Version]
  --> device_disclosure

  supply_chain[Supply Chain Attack]
  --> malicious_app

  compromised_distribution[Compromised Distribution]
  --> supply_chain

  compromised_developer[Compromised Developer]
  --> supply_chain

  malicious_dependency[Malicious Dependency]
  --> supply_chain

  malicious_dev[Malicious Developer]
  --> malicious_app

  side_channel[Side-Channel]
  --> device_disclosure

```

*Legend: trapezoid means all inputs necessary to carry out attack (AND gate).*

#### Privilege Escalation

Malware on the user's device may use an operating system level privilege
escalation vulnerability to read keychain items and database files. We can't
defend against OS level privilege-escalation vulnerabilities.

#### Security Misconfiguration

A bug in the app's source code may be exploited by malware on the user's device
to steal secret keys (e.g. by exploiting incorrect keychain item permissions).
We defend against security misconfigurations by requiring code reviews for all
changes. Open source code serves as an additional defense-in-depth measure
against security misconfigurations.

#### Malicious App Version

Installing a malicious SealVault version can compromise users' secret keys.

##### Supply Chain Attack

Supply chain attacks may target app distribution (how users acquire the app
bundle), the developers of the application or application dependencies (what
goes in the bundle).

##### Compromised Developer

The Apple ID that can submit new app versions is hardened with the following
measures:

- Long random unique password.
- Two-factor authentication enabled.
- Strong device passcodes.
- Trusted phone number hardened against SIM swapping.
- Recovery key enabled to disable account recovery through Apple support.  The
recovery key is stored in a bank safe.

The App Store review process provides a defense in depth measure as the time
delay between submitting and releasing app version gives time to react in case
the Apple ID is compromised.

##### Compromised Distribution

We rely on the iOS App Store for secure app distribution. 
We don't trust application assets that aren't distributed through the App Store.

##### Malicious Dependency

We rely on dependency pinning and Github's supply chain security
[features](https://github.com/features/security/software-supply-chain) to secure
our dependencies.

JavaScript being a popular, interpreted language with a global context and a
micro package-style ecosystem is especially vulnerable to supply chain attacks.
We don't have any JavaScript dependencies due to the prevalence of supply chain
attacks in the ecosystem.

##### Malicious Developer

Open source code and [reproducible builds](https://reproducible-builds.org/)
would protect against malicious SealVault developers.

While our code is open source, the iOS platform makes it [very
difficult](https://core.telegram.org/reproducible-builds##reproducible-builds-for-ios)
to produce reproducible builds and to support this feature SealVault developers
would have to work with jailbroken devices which would open up attack vectors on
the developers. We don't currently support reproducible iOS builds for this
reason, but will introduce reproducible iOS builds as soon as it's possible to
verify them without jailbroken devices.

---

#### Side-Channel

The secret key can accidentally leak through a vector that wasn't intended to
make it possible to access the secret key.

```mermaid
flowchart BT

  ui_disclosure[UI Disclosure]
  --> side_channel[Side-Channel]

  hw_channel[HW Channel]
  --> side_channel

  physical_access[Physicial Access]
  --> hw_channel

  hw_vulnerability[HW Vulnerability]
  --> hw_channel

  sw_channel[/SW Channel\]
  --> side_channel

  passive_sw_channel[/Passive\]
  --> sw_channel

  active_sw_channel[/Active\]
  --> sw_channel

  os_vuln[OS Vulnerability]
  --> passive_sw_channel

  malware[Malware on Device]
  --> passive_sw_channel

  exploit[Exploit]
  --> active_sw_channel

  remote_attack[Remote Exploit]
  --> exploit

  malware
  --> exploit

  app_vuln[App Vulnerability]
  --> active_sw_channel

```

#### UI Disclosure

In a UI disclosure attack, the attacker learns the secret key from its display 
in the user interface. There are several ways this can happen:

- The attacker observes the secret in the UI when it is displayed either
  directly viewing the user's screen either in person or remotely through a
  recording like a CCTV camera.
- The secret is visible when the user takes a screenshot or when the operating
  takes a screenshot as the app goes in the background and the attacker can
  access the screenshot.
- The secret as part of the UI state is saved in an insecure location that the
  attacker can access.[^10]

#### Hardware Side-Channel

In a hardware side-channel attack, an attacker that can take hold of a device to
perform measurements during the execution of the application to recover secret
keys or they can use a hardware vulnerability (e.g.
[Meltdown](https://meltdownattack.com/)) to recover secret keys from the
application with their malware running on the device.

#### Software Side-Channel

In a software side-channel attack, an attacker can write code that can either
passively observe the execution of the application or actively interact with
the application to recover secret keys. 

##### Passive Software Side-Channel

In a passive software side-channel attack the operating system leaks information
to the malware on the device about the application without the malware
interacting with the application. Examples: 

1. Malware can read the application's memory.
2. Malware can take a screenshot of the application. 
3. Clipboard snooping.

##### Active Software Side-Channel

In an active software side-channel, an attacker can utilize a legitimate way to
interact with the application to recover secret keys. The most prevalent active
software side-channel attacks are [timing
attacks](https://timing.attacks.cr.yp.to/) where the attacker measures the
response time of the application to recover secret keys.

#### Side-Channel Defenses

##### Generic Defenses

We mitigate side-channel attacks by

1. Storing all user data encrypted on disk.  
1. Having an additional layer of encryption for secret keys inside the database
   to avoid accidentally storing them in plain text in memory or in temporary
   files created for logs and caches created by the database.
1. Storing [key-encryption-keys](./data.md##secret-key-encryption-keys) in the
   local iOS keychain which is
   [protected](https://support.apple.com/en-ie/guide/security/secb0694df1a/web)
   by the iOS Secure Enclave HSM.
1. Keeping secrets stored in long-lived data structures of the application
   encrypted.
1. Implementing all functionality that needs access to secret keys in our Rust
   code inside designated modules to make it easy to follow data flows. Secret
   values are zeroized on drop and stored on the heap to avoid leaving
   unreachable copies one move.  Secret values have neither `Debug` nor
   `Display` implementations to prevent leaking them in logs.

##### UI Disclosure

We prevent disclosing secret keys through the UI by never displaying them.

##### Clipboard Snooping

We prevent accessing secret keys through the clipboard by never allowing the
user to copy them.

##### Timing Side-Channel

We mitigate timing attacks by 

1. Using constant-time cryptographic implementations.
2. Not branching based on secret values in application code, unless it's a fatal
   error. Conditions are checked with constant time comparison.
3. Rate limiting cryptographic operations that can be initiated by third-party
   code without user interaction to mitigate attacks like
   [Hertzbleed](https://www.hertzbleed.com/) that can bypass constant-time
   safeguards, but need a large sample size.[^15]
4. Disabling cryptographic operations that can be initiated by third-party code
   without user interaction when the application is in the background.
6. Scoping secrets used in cryptographic operations that can be initiated by
   third-party code without user interaction to specific applications through
   [dapp keys](./dapp-keys.md).

---

### Backup Disclosure

In order to learn the secret key from a backup, the attacker must acquire the
encrypted backup file which stores the secret keys in addition to the [KDF
secret](./backup.md##kdf-secret) and the [backup
password](./backup.md#backup-password) that are needed to decrypt the backup
file. To reiterate, as opposed to seed phrases, compromising the [backup
password](./backup.md##backup-password) won't lead to secret key disclosure by
itself since the secret keys are not derived from the backup password.

```mermaid
flowchart BT

  encrypted_backup_disclosure[Encrypted Backup Disclosure]
  --> backup_disclosure[/Backup Disclosure\]

  social_engineering[Social Engineering]
  --> encrypted_backup_disclosure
  
  icloud_storage_compromise[iCloud Storage Compromise]
  --> encrypted_backup_disclosure
  
  apple_id_compromise[Apple ID Compromise]
  --> encrypted_backup_disclosure
  
  kdfs_disclosure[KDF Secret Disclosure]
  --> backup_disclosure
  
  apple_id_compromise
  --> icloud_keychain_access[/iCloud Keychain Access\]
  
  device_passcode_compromise[Device Passcode Compromise]
  --> icloud_keychain_access
  
  icloud_keychain_access
  --> kdfs_disclosure

  icloud_keychain_compromise[iCloud Keychain Compromise]
  --> kdfs_disclosure
  
  backup_pwd_disclosure[Backup Password Disclosure]
  --> backup_disclosure

  storage_access[Storage Access]
  --> backup_pwd_disclosure

  social_engineering2[Social Engineering]
  --> backup_pwd_disclosure

  side_channel[Side-Channel]
  --> backup_pwd_disclosure

  ui_disclosure[UI Disclosure]
  --> side_channel

  clipboard_snooping[Clipboard Snooping]
  --> side_channel
```

#### Encrypted Backup Disclosure

Encrypted backup files are stored in iCloud Storage. In order to gain access to
an encrypted backup file an attacker must

1. compromise a user's Apple ID or 
1. compromise the iCloud Storage service's security controls or
1. trick a user into extracting an encrypted backup from the app-specific iCloud
   Storage and handing it over to the attacker.

We can't defend against any of these attacks, but we note that extracting an
encrypted backup from the app-specific iCloud Storage is a challenging task that
requires a technically advanced user and those users are less likely to fall
subject to trickery in this regard.

#### Backup Password Disclosure

##### Storage Access

The attacker may learn a user's backup password by directly accessing the user's
choice of [storage](./backup.md#self-custody-password-storage).  We can't
prevent access to the backup password beyond advising the user on secure storage
practices.

##### Social Engineering

An attacker may acquire a user's backup password by deceiving the user through
social engineering. We can't defend against this beyond warning the user never
to give out the backup password to anyone.

##### UI Disclosure

The user can view the backup password any time in the application settings on
the device after biometric authentication for reasons explained
[here.](./backup.md#self-custody-password-storage) We mitigate [UI
disclosure](#ui-disclosure) of the backup password by hiding it by default and
requiring the user to reveal it manually by pressing a button.

We prevent the backup password from leaking into snapshots when the app goes
into the background by hiding it from view when the corresponding [system
event](https://developer.apple.com/library/archive/qa/qa1838/_index.html) is
fired.

We prevent the backup password from being saved insecurely as part of the UI
state by removing it from the UI state when the application goes in the
background.

There is no officially supported method to prevent taking a screenshot on iOS,
only the private `_UITextLayoutCanvasView` method and various hacks that may
break with any iOS release, therefore we take no measures against the user
taking a screenshot of the revealed backup password.

##### Clipboard Snooping

The user can copy the backup password any time in the application settings on
the device after biometric authentication for reasons explained
[here.](./backup.md#self-custody-password-storage)

Malicious apps can steal backup password by accessing the clipboard after the
user copied the backup password and switched to the malicious app. As a
mitigation measure, iOS warns the user when an app accesses the clipboard if
it's not initiated through a paste action by the user [since iOS
15.](https://developer.apple.com/videos/play/wwdc2021/10085/?time=360) We can't
defend against the user pasting the backup password into a malicious app.

---

## Approval Spoofing

In an approval spoofing attack, the user authorizes a transaction with different
parameters than they intended to, or the user performs an action which leads to
authorizing a transaction without being aware of authorizing a transaction.

The protected assets are a user's native, fungible tokens and non-fungible
tokens.

### Phishing and Social Engineering

```mermaid
flowchart BT
  phishing[Phishing]
  --> approval_spoofing[Approval Spoofing]

  single_message[Single Message]
  --> phishing[/Phishing\]

  fraudulent_dapp[Fraudulent Dapp]
  --> phishing
  
  social_engineering[Social Engineering]
  --> approval_spoofing

  interactive_medium[Interactive Medium]
  --> social_engineering[Social Engineering]

  fake_data[Fake Blockchain Data]
  --> social_engineering

  compromised_dapp[Compromised Dapp]
  --> approval_spoofing

```

#### Phishing

Phishing is a type of social engineering attack where the attacker prompts the
user to perform an action advantageous to the attacker with a single message (as
opposed to a conversation in other social engineering attacks).

Phishing attacks for approval spoofing rely on prompting a user to interact with
a fraudulent dapp crafted to produce fraudulent transactions.  For example a
fraudulent dapp can ask a user to perform an off-chain signature in order to
qualify for an airdrop, but instead it requests a
[signature](./in-page-provider.md#signatures) that lets the attacker transfer
the user's tokens.

SealVault offers two mitigations for phishing:

1. When a user [connects a new dapp](./in-page-provider.md#new-dapp-flow) for
   the first time, the in-page provider asks the user through a dialog if they
   want to add this new dapp, creates a new dapp key for the dapp and connects
   the new dapp key. Defaulting to creating a new dapp key and connecting that
   by default protects the user from phishing attacks that rely on
   misidentifying the dapp that the user interacts with.
2. When a user [cross-connects](./cross-connect.md) a key to a dapp, we reduce
   approval decisions to payment, pledge a token, or sign in. If we cannot
   guarantee the outcome, we refuse the request and prompt the user to continue
   with the [dapp key.](./dapp-keys.md)

#### Social Engineering

A social engineering attack relies on a crook tricking the user to execute a
transaction. A novel social engineering threat for Web3 users is that crooks may
fake transactions to establish trust with a victim or a trade may be faked to
prompt copy trades.

!!! warning "WIP"

    This section is still work in progress.

---
### Compromised Dapp

An honest dapp may become compromised by an attacker changing its smart contract
or front end to produce fraudulent transactions.  For example, a compromised
front end may prompt the user to approve transactions with a different smart
contract than they intended to.

```mermaid
flowchart BT
  malicious_frontend[Malicious Frontend]
  --> compromised_dapp[Compromised Dapp]

  malicious_sc[Malicious Smart Contract]
  --> compromised_dapp

  supply_chain[Supply Chain Attack]
  --> malicious_sc

  supply_chain
  --> malicious_frontend

  malicious_dependency[Malicious Dependency]
  --> supply_chain

  malicious_dev[Malicious Developer]
  --> supply_chain

  compromised_dev[Compromised Developer]
  --> supply_chain

  clickjacking[Clickjacking]
  --> malicious_frontend

  mitm[Man-In-The-Middle]
  --> malicious_frontend

  xss[Reflected XSS]
  --> malicious_frontend
```

#### Supply Chain Attack

SealVault mitigates supply chain attacks on dapps with [dapp
keys](./dapp-keys.md) that limit the damage a compromised dapp can do to the
assets belonging to that dapp.

#### Clickjacking

!!! warning "WIP"

    This section is still work in progress.

#### Man-In-The-Middle

We mitigate man-in-the-middle attacks on dapps by disallowing transactions and
signatures for dapps that were served over HTTP.[^20]

#### Reflected XSS

The application must pass data to the dapp frontend JavaScript which could open
up a reflected XSS vector for messages from remote APIs.

We defend against reflected XSS by converting messages to binary JSON
represented as hexadecimal string literals before sending them to the dapp
frontend.  This is safe because it's not possible to break out of a string
literal enclosed in `"..."` with the hexadecimal character set `[0-9A-Fa-f]`.

[^0]:
    Users can export keys, they just can't copy them directly from the application
    interface. The design of the export feature is
    [WIP.](https://github.com/sealvault/sealvault/issues/39)

[^10]: 
    See [CVE-2022-32969](https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-2022-32969)
    for a recent example.

[^15]:
    This is a [todo.](https://github.com/sealvault/sealvault/issues/31)

[^20]:
    This is a [todo.](https://github.com/sealvault/sealvault/issues/30)
