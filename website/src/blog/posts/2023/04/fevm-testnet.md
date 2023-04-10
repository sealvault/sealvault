---
slug: 2023/04/fevm-testnet
date: 2023-04-09
authors:
- agostbiro

links:
- dev-docs/design/dapp-keys.md
- dev-docs/design/cross-connect.md
---

# Dev Update: Filecoin FEVM Support & Upcoming Features

Hi folks, this is a quick development update.

I’ve made some under the hood improvements to unblock FEVM support and the
Filecoin Hyperspace testnet is now supported in the iOS beta for SealVault.
There is no NFT support and no automatic custom token discovery support yet for
FEVM due to lack of [Ankr Advanced
API](https://www.ankr.com/docs/advanced-api/overview/) support. We'll eventually
add these through standard Ethereum RPC methods (tracking issues:
[#112](https://github.com/sealvault/sealvault/issues/112) and
[#113](https://github.com/sealvault/sealvault/issues/113)). If you wanna see
other chains supported, please open a feature request on
[GitHub.](https://github.com/sealvault/sealvault)

[This
release](https://github.com/sealvault/sealvault/blob/main/CHANGELOG.md#ios-beta-v080)
also brings increased transaction reliability by using gas oracles to estimate
gas fees and gradually increasing gas price allowance to make sure transactions
don't get stuck in the mempool.

<!-- more -->

SealVault is a combination of a password manager and MetaMask and it currently
only supports interacting with dapps through so called [dapp
keys.](https://sealvault.org/dapp-keys/) Dapp keys are externally owned accounts
bound to a domain. Dapp keys are cool, because they are secure by default and
can do automated transaction approval, but due to how the Ethereum ecosystem
evolved, they don’t cover all use cases.

The next step for SealVault is support for connecting keys to multiple dapps (so
called [cross-connect](https://sealvault.org/dev-docs/design/cross-connect/)).
Normally wallets support this by having the user review transaction details and
offer warnings if something looks fishy. We're trying to do better than this and
I'm working on being able reduce transaction approval to sign in and payment
decisions where users can trust the outcome (think Apple Pay).

If you wanna try the iOS SealVault beta, you can install the Testflight version
[here.]( https://testflight.apple.com/join/EHQYn6Oz) If you do, please share
your experience on [Telegram](https://t.me/agostbiro) or on
[GitHub.](https://github.com/sealvault/sealvault/discussions)