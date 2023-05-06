---
slug: 2023/05/dapp-isolation-mechanisms
date: 2023-05-06
authors:
  - agostbiro

links:
  - dev-docs/design/dapp-keys.md
---

# Dapp Isolation Mechanisms in the Ethereum Ecosystem



*TLDR: Requiring manual approval for every signature request can hinder good
social and gaming experiences. We can automate signature approval with dapp
isolation mechanisms such as session keys. Dapp isolation can not only improve
user experience, but it can also ensure security when testing new dapps. This
could reverse the negative trend of users being reluctant to experiment with new
things and ultimately benefit the ecosystem as a whole.*

<!-- more -->

# What is Dapp Isolation

Assume a universe with two tokens Doken and Goken, and two dapps
[dapp.com](http://dapp.com/) and [gapp.com](http://gapp.com/). Both dapps try to
spend both tokens, but the owner only wants to spend Dokens on
[dapp.com](http://dapp.com/) and Gokens on [gapp.com](http://gapp.com/). How can
this be enforced?

One way is to require interpreting all signature requests and have the user or
the wallet block requests that want to spend Dokens on
[gapp.com](http://gapp.com/) or Gokens on [dapp.com](http://dapp.com/). This is
the default solution in the Ethereum ecosystem, but it’s very difficult to
execute securely for both humans and computers. In fact, determining the outcome
of all possible signature requests with certainty when off-chain signatures [can
lead to](https://sealvault.org/dev-docs/design/token-transfer-traces/) on-chain
transactions is probably an unsolvable problem. The best wallets can do
currently is offer warnings.

Another way to guarantee that Dokens can be only spent on
[dapp.com](http://dapp.com/) and Gokens on [gapp.com](http://gapp.com/) is to
use isolation mechanisms such as session keys. Isolation mechanisms flip the
problem from denying unintended requests to only allowing intended requests.
With isolation mechanisms, we can guarantee that the invariant holds, so we can
eliminate transaction approval.

Isolation mechanisms solve an important UX and security problem, but since they
aren’t part of the Ethereum protocol, they come with some caveats. This posts
lists the various isolation mechanisms and discusses their strengths and
limitations.

# Isolation Boundaries

A dapp is a website that interacts with smart contracts through its front end
code. Users typically identify dapps by their domains. We can isolate dapps
either at the domain level or at the smart contract level.

## Domain Level Isolation

The main advantage of domain level isolation is that it matches how users
identify dapps.

Domain level isolation is not a new concept on the web and it is an integral
part of all web browsers, forming the basis of security mechanisms like cookies
and the same-origin policy.

To implement domain level isolation, we need to determine which domain served
the document that issued a signature request. Web browsers hold this
information, so getting the domain is easy for wallets that are part of web
browsers or integrate with browsers through extensions. They can also pass the
domain to smart contracts as transaction parameters.

Determining the domain that issued a signature request is a much more difficult
problem for wallets that are not directly integrated with the browser. For
example, WalletConnect [states](https://youtu.be/L1KitRiwP8Y?t=727) that they
have an 80% solution which is ok for their intended use (phishing mitigation),
but it's unclear whether it can be relied on for automated signature approval.

## Smart Contract Level Isolation

Smart contract level isolation makes it easy to enforce restrictions on
transactions, but it’s not as straightforward as it sounds. A legitimate smart
contract can be used maliciously e.g. by listing a valuable NFT for a pittance.
This means that it’s not enough to set the isolation boundary on specific
contracts, but the boundary also has to encompass how parameters are passed to
the contracts.

Another issue is that humans do not identify dapps by smart contract addresses
and a dapp may use multiple addresses and addresses may vary across chains. This
means that a wallet wanting to perform smart contract-level dapp isolation
probably needs to maintain a centralized registry that maps dapp names to
addresses. If the dapp identifier mapping needs to be accessed on-chain, that
further complicates things and most likely requires an oracle, unless the
registry is on-chain. However, that introduces the problem of name squatting.

# Dapp Isolation Implementations

This section reviews implementations of dapp isolation currently used or being
developed in the ecosystem.

## Off-Chain Session Keys

Off-chain session keys are the most widely deployed mechanism for automated
signature approval in the ecosystem currently.

Many dapps with traditional backends have adopted digital signatures for
authorization. Off-chain session keys are used to automate signature approval
for these backends.

Session keys are ephemeral keys that are randomly generated within the
application that intends to use them. The address owner then signs a message
that grants the random key certain permissions. These permissions are typically
application-specific, but standards like [UCANs](https://ucan.xyz/#delegation)
are emerging.

Off-chain session keys do not control assets, so security questions around them
are lower impact. Still, I believe that the potential for unexpected outcomes
from interactions between different permission systems is underexplored.

Examples:

- [Ceramic](https://blog.ceramic.network/capability-based-data-security-on-ceramic)
  - [Farcaster Delegated Signers](https://www.youtube.com/watch?v=ZzySey1azWM) -
  [Lit Protocol Session
  Keys](https://developer.litprotocol.com/sdk/explanation/walletsigs/sessionsigs/)
  - [Sequence Session
  Keys](https://docs.sequence.xyz/wallet/guides/session-keys) - [Sign-In With
  Ethereum + Session
  Keys](https://blog.spruceid.com/from-sign-in-with-ethereum-to-session-keys/) -
  [UCANs](https://ucan.xyz/#delegation)

## Session Keys for Smart Contract Wallets

*I don’t have the full picture on SCW session keys, so I’m just thinking out
loud here.*

Session keys for smart contract wallets (SCW) are a new mechanism. Many SCW
teams are working on session keys, but I’m not aware of any production
implementations yet.

The idea is the same as with off-chain session keys: an ephemeral key is created
by a dapp, the SCW assigns some permissions to the ephemeral key after which the
dapp can produce signatures for a limited set of transactions using the session
key without requiring the user’s approval.

SCW session keys can use [EIP-4337](https://eips.ethereum.org/EIPS/eip-4337)
paymasters by @vbuterin et al. so the ephemeral key can submit transactions
without holding tokens to pay for gas fees.

A straightforward implementation of SCW session key permissions is to restrict
the contract methods and contract addresses the session key can call. As
mentioned earlier, a legit smart contract can be used maliciously e.g. by
listing a valuable NFT for a pittance. Therefore, in addition to checking the
address and the methods called by a transaction, the SCW implementation has to
be able to interpret the method parameters as well to prevent abuse.

Interpreting parameters for standard token methods seems feasible, but it’s
unclear if a generic permission system can be designed that allows SCW session
keys for data other than standard tokens (e.g. custom game state or off-chain
signatures). It’s also unclear how the user knows for which dapp they’re
approving permissions and what are the semantics of the permission.

Another approach to permissions is for the dapps to define the permissions they
request. This solves the problem of wallet-defined permissions not being generic
enough, but now wallets have to be able interpret dapp permission requests in
order to let the user make an informed decision.

This has the makings of an N x M problem where dapps have to support many
different wallet permissions and wallets have to support many different dapp
permissions. If that happens, the burden of interpreting dapp permission
requests will most likely fall on users and that’d render the security benefits
of session keys moot, so we should start thinking about solutions here.

Wallet examples:

- [Argent](https://www.notion.so/Argent-X-Supporting-On-chain-Games-1ec71fc2b6ad4fe19b8f22cc677838b9)
  (WIP) - [Biconomy with MM Snaps](https://www.youtube.com/watch?v=NBQEtLjN84E)
  (PoC) - [Candide](https://docs.candidewallet.com/develop/wallet/session-keys/)
  (WIP) - [Rollup.id](https://github.com/proofzero/rollupid/issues/2118) -
  [Starknet Burners](https://github.com/dontpanicdao/starknet-burner) (PoC) -
  [ZeroDev](https://docs.zerodev.app/use-wallets/use-session-keys)

Dapp examples:

- [Cartridge.gg](https://www.notion.so/Session-Keys-9e60f92a2f8c4912bd8f61eee3fdfed6)
  (WIP) - [MUD](https://github.com/latticexyz/mud/issues/327) (WIP)

## Dapp Keys

Dapp keys are externally owned accounts (EOA) that are unique to a domain.
Binding an EOA to a dapp by domain is an effective isolation mechanism that
enables automated signature approval for both on- and off-chain signatures.
Since a dapp key is just an EOA, it can hold assets and it works by default for
all dapps on all chains.

Users authorize dapps to use their assets by transferring them to the dapp key
from another address.

Dapp key implementations are more complex than off-chain session keys since they
need to be backed up and they need to receive tokens for gas fees.

Having to transfer tokens to dapp keys can be prohibitive on L1, but it’s less
of a problem on cheap L2s. [EIP-3074](https://eips.ethereum.org/EIPS/eip-3074)
and sponsored transactions by @SamWilsn et al.  would eliminate the need to
transfer tokens for gas fees.

One further challenge with dapp keys is that many apps assume one EOA per user
when using the user's on-chain history for authorization purposes. However, this
trend seems to be changing with solutions like [Delegate
Cash](https://delegate.cash/). Additionally, having many addresses can cause
headaches when preparing tax returns.

A standard for dapp key derivation from seed phrases was proposed in
[EIP-1775](https://eips.ethereum.org/EIPS/eip-1775) by @Bunjin and @danfinlay,
but the proposal seems stagnant. I know of two dapp key implementations in the
wild, but neither follow [EIP-1775](https://eips.ethereum.org/EIPS/eip-1775):

- [Dark Forest](https://blog.zkga.me/df-04-faq) (manual backup) -
  [SealVault](https://sealvault.org/dapp-keys/) (automatic backup; we’ve
  implemented this)

## WebAuthn Signers

The WebAuthn protocol introduces passwordless authentication to the internet
using public key cryptography with
[passkeys](https://fidoalliance.org/passkeys/). Last year, Apple, Google, and
Microsoft
[announced](https://fidoalliance.org/apple-google-and-microsoft-commit-to-expanded-support-for-fido-standard-to-accelerate-availability-of-passwordless-sign-ins/)
a joint effort to accelerate its adoption, and it is now natively supported in
all major browsers. SCWs can be modified to verify signatures from WebAuthn keys
on the chain.

WebAuthn keys are scoped to domains for phishing protection and privacy.
Different domains have different keys.

On the one hand scoping keys to domains is a useful property for SCWs, because
it can be used to verify on chain which dapp (domain) the signature was produced
for.

On the other hand, scoping keys to domains makes it difficult to manage WebAuthn
signers for SCWs. Consider the case when a smart contract wallet is created with
a WebAuthn signer on [webauthn-scw.com](http://webauthn-scw.com/). Now if that
smart contract wallet is to be used on [some-dapp.com](http://some-dapp.com/),
[some-dapp.com](http://some-dapp.com/) has to embed
[webauth-scw.com](http://webauth-scw.com/) as an iframe in order to facilitate
that.

With WebAuthn, each signature requires a UI interaction by the user, so WebAuthn
keys cannot be directly used for automatic transaction approval. Instead, an
additional delegation step must be used from the WebAuthn key to a session key.

Examples:

- [Cartridge.gg](https://hackmd.io/@tarrence/Hkjrm8cJj) - [AA Passkey Wallet
  PoC](https://github.com/itsobvioustech/aa-passkeys-wallet)

Related:

- [Secure Payment
  Confirmation](https://www.w3.org/TR/secure-payment-confirmation/) for
  cross-origin WebAuthn - [How ICP uses
  WebAuthn](https://medium.com/dfinity/web-authentication-and-identity-on-the-internet-computer-a9bd5754c547)

*An earlier version of this post has appeared on the [Ethereum Magicians
forum.](https://ethereum-magicians.org/t/dapp-isolation-mechanisms/13611)*