---
slug: 2023/05/ethereum-signature-approval
date: 2023-05-08
authors:
  - agostbiro

links:
  - dev-docs/design/dapp-keys.md
  - dev-docs/design/cross-connect.md
---

# What if Ethereum Signature Approval Was as Simple as Apple Pay?

## The Problem

When users interact with dapps in the Ethereum ecosystem, they have to approve
signature requests from the dapps in their wallets. This comes with security and
UX challenges. The security challenge is that different dapps have different
types of signature approval requests and malicious dapps can exploit this to
trick users into approving signature requests that they would not approve
otherwise. The UX challenge is that while it’s ok to require explicit approval
for each interaction in financial applications, it becomes cumbersome in social
apps and games.

<!-- more -->

<figure markdown>
![12 different Ethereum payment approval requests](/assets/images/blog/2023/05/many-ways-of-ethereum-payments.png){ loading=lazy }
<figcaption>
The many ways of making payments in the Ethereum ecosystem. Pretty much every
dapp uses a distinct verb and approvals are often multi-step.
</figcaption>
</figure>

## Current Solutions

### Wallet Firewalls

The most recent attempt to address the security problem are so-called wallet
firewalls. Firewalls categorize signature requests as safe, potentially
dangerous or dangerous.

Wallet firewalls are a much welcome development, but they are not a long-term
solution. Firewalls rely on prior threat intelligence to make security
decisions, which makes them a probabilistic solution. This means that they
either have too many false positives or too many false negatives. If the
firewall gives too many warnings, users get desensitized, and if it’s too lax,
then it's ineffective.

Wallet firewalls understandably prefer to err on the side of caution and
minimize false negatives. Due to this tradeoff, warnings are often shown for
legitimate signature requests. Users are then expected to interpret the factors
that lead to the warnings in order to decide whether to proceed.

Attacks typically place victims under time pressure, so victims are more likely
to ignore warnings than normally. This means that warnings are the least
effective when they’re needed the most.

Warnings are not only poor security, but they’re also bad UX: non-technical
users are required to make decisions for which they are not qualified, and even
advanced users become desensitized to warnings due to the inevitably high number
of false positives.

Finally, if every new dapp comes with a warning, that discourages
experimentation, so even if firewalls reduce harm from attacks, they can hamper
the growth of the ecosystem.

<figure markdown>
![Warnings from 3 different wallet firewall products for 3 different legitimate signature requests](/assets/images/blog/2023/05/firewall-warnings.png){ loading=lazy }
<figcaption>
Warnings from wallet firewall products for legitimate signature requests.
</figcaption>
</figure>

### Session Keys

[Session keys for smart contract
wallets](https://sealvault.org/blog/2023/05/dapp-isolation-mechanisms/#session-keys-for-smart-contract-wallets)
(SCWs) are a new mechanism that enables automatic signature approval to improve
UX for social and gaming applications.

A session key is an ephemeral key created by a dapp that the SCW assigns some
permissions by restricting the contract methods and contract addresses the
session key can call. After this, the dapp can produce signatures for a limited
set of transactions using the session key and send them directly to the wallet’s
smart contract for execution without requiring the user’s approval.

Session keys solve the UX problem, but they introduce a novel security problem
similar to, but broader in scope than spender approval exploits. First, when
approving the session key request, the user has to understand what application
the smart contract belongs to and what the specific method does. But this is not
enough. A legit smart contract can be used maliciously e.g. by listing a
valuable NFT for a pittance. Therefore, in addition to checking the address and
the methods called by a transaction, the SCW implementation has to be able to
interpret the method parameters as well to prevent abuse.

Interpreting parameters for standard token methods seems feasible, but it’s
unclear if a generic permission system can be designed that allows session keys
for data other than standard tokens (e.g. custom game state or off-chain
signatures).

The most likely outcome is that session keys will have to be either restricted
to interactions with standard tokens for security, or SCWs will have to maintain
an allow list of smart contract addresses and methods that are deemed to be
safe. Allow lists work, but they put new applications at a disadvantage and thus
hamper innovation.

## How Can We Do Better?

First, we have to realize that users cannot be expected to learn the
idiosyncrasies of every dapp they’re using. This means that we need to
standardize signature approvals in the Ethereum ecosystem to solve the security
problem.

Second, we have to realize that it’s not possible to standardize signature
approvals without breaking backwards compatibility. So what then? We need to
find a way that lets us progressively introduce standardized signature approval
while providing users with an automatic signature approval mechanism that’s safe
by default.

Standardization solves the security problem when manual approval is unavoidable.
An automatic signature approval mechanism, when designed without sacrificing
security, can not only fix the UX problem, but can also serve as a safe fallback
mechanism for illegible signature requests.

When it comes to standardizing signature approval, we should start with what
internet users already know: sign in and payments. These cover most use cases
that need manual approval. The only thing that’s missing is spender approval.

### Sign In

Internet users are familiar with the concept of signing in to a website with a
password or through a social provider. Recently, passwordless logins based on
[WebAuthn](https://developer.mozilla.org/en-US/docs/Web/API/Web_Authentication_API)
started to take off.

<figure markdown>
![Passwordless login on iOS with WebAuthn](/assets/images/ios-safari-passkey.png){ loading=lazy class="img-max-height-600"}
<figcaption>
Passwordless login on iOS with WebAuthn.
</figcaption>
</figure>

Proving ownership of an address in the Ethereum ecosystem is very similar from a
UX perspective to passwordless sign in. Therefore, we should present signature
approval requests to prove ownership of an address as sign in requests, even if
they are sometimes authorization requests from a technical perspective (as
opposed to authentication requests).

If the sign in message is not a [Sign-In with
Ethereum](https://eips.ethereum.org/EIPS/eip-4361) message, then the original
message needs to be displayed to the user since it might have legal implications
(e.g. attesting not to be a U.S. resident on DEXes for compliance reasons).

### Payment Approval

Internet users are familiar with making online payments. Payment approval type
requests, let that be making a swap, minting an NFT or supplying collateral for
a loan, should be as simple as Apple Pay.

<figure markdown>
![Apple Pay prompt on iOS](/assets/images/apple-pay-demo.png){ loading=lazy class="img-max-height-600"}
<figcaption>
Apple Pay prompt on iOS.
</figcaption>
</figure>

If the user receives a standard token in exchange for the payment, the payment
is akin to a trade and we display both the spent and received tokens.

### Spender Approval

[Spender
approval](https://sealvault.org/dev-docs/design/in-page-provider/#spender-approvals) is
a novel concept introduced by Ethereum. Its purpose is to let decentralized
exchanges settle trades based on users' orders. Spender approvals are similar to
payment approvals, but they’re different in that they’re an ongoing, but
reversible commitment. It’s not enough to handle approval, wallets should keep
track of approvals and support revocation too.

Spender approval is a challenging concept to convey to users. We’ll figure out
how to best present spender approvals with the help of the [Secure Design
Working Group](https://github.com/ChainAgnostic/secure-design/discussions/4).

### Dapp Keys

It’s not possible to reduce all signature approval requests in the wild to sign
in, payment or spender approval requests and they don’t solve the UX challenge
for games and social apps. So in addition to standardizing signature requests,
we need to introduce a new primitive that works like session keys, but is safe
by default. This primitive is dapp keys.

> [W]allets should start moving toward a more natively multi-address model (eg.
creating a new address for each application you interact with could be one
option) - [Vitalik](https://vitalik.ca/general/2023/01/20/stealth.html)

[Dapp keys](https://sealvault.org/dapp-keys/) are externally owned accounts
(EOA) that are unique to a domain. Binding an EOA to a dapp by domain is an
effective [isolation
mechanism](https://sealvault.org/blog/2023/05/dapp-isolation-mechanisms/) that
enables automatic signature approval. Since a dapp key is just an EOA, it can
hold assets and it works by default for all dapps on all chains. Users authorize
dapps to use their assets by transferring them to the dapp key from another
address.

<!--
<figure markdown>
![A user profile with a wallet key and multiple dapp keys in the SealVault iOS app](/assets/images/screenshots/profile-view.png){ loading=lazy class="img-max-height-600"}
<figcaption>
A user profile with a wallet key and multiple dapp keys in the SealVault iOS app
</figcaption>
</figure>
-->
<figure markdown>
![Apple Pay prompt on iOS](/assets/images/blog/2023/05/dapp-keys.png){ loading=lazy class="img-max-height-600"}
<figcaption>
A user profile with a wallet key and multiple dapp keys in the SealVault iOS app
</figcaption>
</figure>

Dapp keys are safe by default, because, as opposed to session keys, they use an
authorization method (token transfers) that is familiar to users and that cannot
be exploited by malicious dapps. With dapp keys, social and gaming dapps can
benefit from automatic signature approval without restrictions and users can
securely try out new dapps without confusing warnings.

## How to Get There

### Dapp Keys

[Dapp keys](https://sealvault.org/dapp-keys/) are already implemented in
[SealVault](https://sealvault.org/) and the
[code](https://github.com/sealvault/sealvault) is available under an open source
license. SealVault is not a seed-phrase based wallet, but there exists
[ERC-1775](https://eips.ethereum.org/EIPS/eip-1775) that describes how to derive
a key from a seed phrase that is bound to a domain that can be of interest to
other wallets.

There are two remaining challenges with dapp keys. The first is that having to
transfer tokens for gas fees to dapp keys can be prohibitive on L1 (it’s less of
a problem on cheap L2s). Rolling out
[EIP-3074](https://eips.ethereum.org/EIPS/eip-3074) and sponsored transactions
would eliminate the need to transfer tokens for gas fees.

The second challenge is that many dapps assume one EOA per user and some [data
portability
patterns](https://sealvault.org/dev-docs/design/cross-connect/#use-cases) have
evolved to require connecting the same key to different
dapps[.](https://sealvault.org/dev-docs/design/cross-connect/#use-cases) This
means that implementations must support connecting dapp keys to other dapps,
just like regular wallets, which brings us to standardized signature approval.

### The Signature Approval Engine

Standardized signature approval means we provide guarantees about outcomes. If a
user approves a sign in request, that won’t lead to a token transfer. If a user
approves a payment request, only the exact amount of tokens displayed will be
transferred.

!!! note

    We have to make a caveat here that it’s only possible to make such guarantees
    about standard tokens since their state changes must fire standardized events
    that we can detect in simulation. For example, a game might have an asset that
    implements the ERC-721 interface, but when the asset is transferred, some custom
    game state changes as well. This is not necessarily a bad thing, but if it’s
    exploitable in a way that the user intends to make the transfer, but not the
    custom state change, then we have to view that as a vulnerability of the dapp.

The first step towards providing such guarantees is understanding what can go
wrong. This we have accomplished at [SealVault](https://sealvault.org) with a
[fraudulent transaction attack
tree](https://sealvault.org/dev-docs/design/attack-tree/) and a [formal
specification](https://sealvault.org/blog/2023/04/token-transfer-tla/) of
Ethereum token transfers with TLA+ (both available under open source licenses).
The attack tree helped us focus our efforts on fixing signature approval. The
formal specification helped us exhaustively identify the 42 ways a token can be
transferred with a combination of on- and off-chain signatures, spender
approvals and meta transactions.

The [formal
specification](https://sealvault.org/blog/2023/04/token-transfer-tla/) gives us
confidence for the next step which is implementing an **open source engine**
that lets us classify signature requests as sign in, payment, spender approval
or unknown. If we cannot detect the signature request type, we advise users to
continue with a dapp key for their safety. The engine also extracts the data we
need to present to users from the signature requests. In the future, we can also
use the engine to bundle multistep signature approval requests into one payment
approval request.

There are two types of signature requests: on- and off-chain signature requests.

An on-chain signature is a signature that can be submitted along with the signed
data through the
[`eth_sendRawTransaction`](https://ethereum.org/en/developers/docs/apis/json-rpc/#eth_sendrawtransaction)
method. The on-chain signature is verified by Ethereum nodes before the
transaction is included in a block. The data signed with on-chain signatures
follows a [standard
format,](https://docs.ethers.org/v5/api/providers/types/#providers-TransactionRequest)
and it can be used to simulate the on-chain changes caused by a signature.

An off-chain signature is a valid signature that Ethereum nodes refuse to accept
for a transaction. Off-chain signatures are
[used](https://sealvault.org/dev-docs/design/token-transfer-traces) for
off-chain auth purposes, [gasless
transactions](https://sealvault.org/dev-docs/design/token-transfer-traces/#meta-transaction)
or for bundling multiple transactions into one ([permit
pattern](https://sealvault.org/dev-docs/design/token-transfer-traces/#permit)).
While the [Sign-In with Ethereum](https://eips.ethereum.org/EIPS/eip-4361)
standard exists for authentication messages, it’s not widely adopted, and many
dapps use ad-hoc messages. There are no standards for gasless transaction or
bundled message formats. These typically use
[EIP-712](https://eips.ethereum.org/EIPS/eip-712) signatures, but
[`personal_sign`](https://docs.metamask.io/wallet/how-to/sign-data/#use-personal_sign)
messages cannot be ruled out either.

Since on-chain signatures follow a standardized format, detecting them is easy
and transaction simulation can be used to extract the data that we have to
present to the user for payment or spender approval. Transaction simulation is
available as a service from many software-as-a-service providers, but these
services are closed source and transaction simulation is [tricky to get
right,](https://zengo.com/zengo-uncovers-security-vulnerabilities-in-popular-web3-transaction-simulation-solutions-the-red-pill-attack/)
so we prefer to have our own open source implementation. We’re going to use
[Reth](https://github.com/paradigmxyz/reth) as a dependency of the engine to
provide transaction simulation and we’ll continue to make contributions to Rust
Ethereum ecosystem packages during development.

In order to interpret off-chain signatures, we need to build custom parsers for
the most commonly used formats in the ecosystem such as [permit
messages,](https://sealvault.org/dev-docs/design/token-transfer-traces/#permit)
[OpenSea Seaport
orders](https://docs.opensea.io/reference/seaport-overview#order) and [OpenGSN
messages.](https://docs.opengsn.org/#architecture) We also need a method that
can rule out if a
[`personal_sign`](https://docs.metamask.io/wallet/how-to/sign-data/#use-personal_sign)
message can lead to a token transfer, otherwise we can present them as sign in
requests.

We’ll start developing the engine as part of the SealVault application’s open
source Rust [code](https://github.com/sealvault/sealvault) to maximize velocity,
but we’ll release it as a **standalone open source project** under an MIT/Apache
2.0 dual license once it stabilizes to make it possible for other wallets to use
it as well. Both EOA and smart contract wallets will benefit from this
regardless of whether they use dapp keys. We’ll also support compiling the Rust
package to WASM so that it can be used from JavaScript to maximize reach.

## Endgame

Once the plan laid out here is accomplished, we’ll have built a safe and smooth
Ethereum signature approval experience with the help of standardized signature
approval and dapp keys that any internet user can use with confidence. Further,
we make it possible with the open source Signature Approval Engine for other
wallets to follow suit as well. 

We'll then drive two efforts to further improve the Ethereum signature approval
experience:

1. A standardization effort a for common format of off-chain signatures that can
   lead to token transfers to further the expand the scope of standardized
   signature requests.
2. The effort to roll out [EIP-3074](https://eips.ethereum.org/EIPS/eip-3074) to
   make it possible to use dapp keys without having to transfer tokens for gas
   fees thanks to sponsored transactions. The simplest way to get this on the L1
   development roadmap is probably to roll it out on a receptive L2 first and
   demonstrate its value.

Getting these through we'll be slow and sluggish, but we believe that
standardizing signature approval requests and providing a safe by default [dapp
isolation
mechanism](https://sealvault.org/blog/2023/05/dapp-isolation-mechanisms/) is
unavoidable to achieve mass adoption of Ethereum and we’re committed to seeing
it through.