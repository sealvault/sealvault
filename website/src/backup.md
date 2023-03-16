# Self-Custody Cloud Backup

SealVault can **automatically back up your keys and profiles to your iCloud
Storage** so that you can restore them if you lose your device or get a new one.
Backups are created when you exit the app.

All backups are encrypted with a strong backup password generated on your
device. You'll need to write down the backup password on paper or save it in a
password manager. The backup password is protected by Secure Enclave and it's
not synced between your devices. 

**It's not possible to recover from iCloud Storage without the backup
password.**

<figure markdown>
![iOS backup settings](./assets/images/screenshots/backup-settings.png){ loading=lazy class="img-max-height-600" }
</figure>

## Rotate 

You can rotate the backup password any time by disabling
and enabling backups anew.

## Two-factor

In addition to the backup password, a secret is stored on your iCloud Keychain
that is required to decrypt your backups. This additional secret protects your
keys in case your backup password is stolen, but it's not possible to decrypt
your backups with this secret alone.

## Technical Docs

- [Data model](./dev-docs/design/data.md)
- [Backup design](./dev-docs/design/backup.md)
