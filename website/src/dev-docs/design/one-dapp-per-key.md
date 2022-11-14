# One-Dapp-per-Key

We believe that the current trend in Web3 clients to make transaction parameters
more legible or reactively catalogue malicious dapps to prevent fraud is
misguided.  Since social attacks rely on a sense of urgency, reactive
methods leave users vulnerable and the burden of understanding the
idiosyncrasies of various blockchains cannot be placed on users.  A [better
approach](./security-model.md#deception-mitigation) is to prevent actions that
can be dangerous to users and disincentivize attackers.

The One-Dapp-per-Key (1DK) model is a novel isolation mechanism for Web3
clients.  As the name suggests, in the 1DK model **one key is only allowed to
approve transactions for one dapp.** This isolation
[prevents](./attack-tree.md#phishing-and-social-engineering) phishing attacks
with fraudulent dapps and [mitigates](./attack-tree.md#compromised-dapp) damage
from compromised dapps by denying them access to data from other dapps.  As an
added benefit, the 1DK model enables **automated transaction approval** which is
necessary to drive Web3 beyond financial applications (like games).

## What Is a Dapp?

A dapp in the 1DK model is a website that interacts with blockchain smart
contracts through its front end code.  A dapp is identified by its [registrable
domain.](https://url.spec.whatwg.org/#host-registrable-domain)

More specifically, when deciding whether a key may perform a transaction
originating from a dapp, we consider two origins to belong to the same dapp if
they are [schemefully same-site.](https://html.spec.whatwg.org/#same-site)
We only allow connecting dapps that were not served over HTTPS in developer
mode.

For example, `https://trade.somedapp.com` and `https://mint.somedapp.com` would
be considered the same dapp, but `https://foo.github.io` and
`https://bar.github.io` would be different dapps because `github.io` is in the
[public suffix list.](https://publicsuffix.org/list/)

The rationale for using the registrable domain is that that's the unit under the
control of the dapp developer.  Further isolation would not improve security,
but it could cause usability issues.

### Embedded Contexts

As explained in the [new cookie RFC
draft:](https://datatracker.ietf.org/doc/html/draft-ietf-httpbis-rfc6265bis-09#section-5.2.1)

> The URI displayed in a user agent's address bar is the only security context
directly exposed to users, and therefore the only signal users can reasonably
rely upon to determine whether or not they trust a particular website. The
origin of that URI represents the context in which a user most likely believes
themselves to be interacting.

Therefore, we derive the dapp identifier from the [top-level
origin](https://html.spec.whatwg.org/#concept-environment-top-level-origin) for
dapps displayed in embedded browsing contexts. This also defends against
[clickjacking](./attack-tree.md#clickjacking) attacks.

For example, the decentralized asset management platform,
[dHEDGE](https://www.dhedge.org/) embeds other dapps like
[Aave](https://aave.com/) and [Uniswap](https://uniswap.org/) on
`app.dhedge.org`.  In the 1DK model, the identifier for both the dHEDGE and the
embedded Aave and Uniswap dapps would be `dhedge.org`.  This means that the key
used for `dhedge.org` could be used to approve transactions for the dHEDGE dapp
accessible on `app.dhedge.org`, and the Aave and the Uniswap dapps *embedded* on
`app.dhedge.org`, but the same key couldn't be used to approve transactions when
the user directly visits `app.aave.com` or `app.uniswap.org`.

Preventing the use of keys associated with embedded contexts when visiting them
directly ensures that removing an embedded dapp from a site removes its access
to other dapps on that site.

## Changing Dapp for Address

The user can change the identifier of a dapp associated with an address if there
are only negligible native tokens or fungible tokens and no non-fungible tokens 
held by that address.
This means that users can 

1. Create an address and associate a dapp with it later which is important to be
   able to sign up for off-chain allow lists prior to mints for example.
2. Use an address with a different dapp if they transfer existing funds away
   first.

The requirement to transfer funds to a different address before changing the
dapp for an address allows us to let users handle unforeseen circumstances while
mitigating social engineering attacks.

## Porting Data

The 1DK model prevents one dapp mutating data that was produced by an other
dapp, but sometimes it's necessary to port such data between dapps.  SealVault
offers two solutions:

1. Standardized tokens (ERC20, ERC721, SPL etc.) can be moved between dapps
   through the SealVault app where informed consent about the transfer's
   consequences can be guaranteed.
2. SealVault allows performing off-chain signatures between dapps (subject to
   [privacy controls](./privacy-model.md)). This means that if somebody wants to
   fork a dapp whose data is not in transferable tokens, they can prompt the
   user for an off-chain signature to verify their ownership and then copy the
   data to their contract.

## Airdrops

There are two types of airdrops: push- and pull-style airdrops.  In a
push-style airdrop, the token creator sends tokens directly to a user address
without any interaction on the user's side.  In a pull-style airdrop, the user
has to approve a transaction or perform an off-chain signature to receive the
goods.

### Push-Style Airdrops

Push style airdrops are compatible with the 1DK model, because they require no
dapp interaction on the user's part, and the user can always transfer tokens
from a 1DK address through the native app UI.

### Pull-Style Airdrops

Pull-style airdrops check the eligibility of the user based on some criteria.
Pull-style airdrops are compatible with the 1DK model, albeit with some caveats.

The eligibility criteria may be the receiver's address, or transferable or
non-transferable tokens held by the receiver address or a combination of these. 
The address criterion is usually determined based on some past activity, like
interactions with a dapp.

In a pull-style airdrop the user has to approve an on-chain transaction or
perform an off-chain signature to receive tokens.  Off-chain signatures pose no
difficulties, as they aren't covered by 1DK restrictions (see [this
FAQ](#what-about-off-chain-signatures) for more).

#### Pull-Style Airdrops w/ On-Chain Transactions

In a pull-style airdrop where the user has to approve an on-chain transaction,
the smart contract may allow performing the transaction with any address or it
may restrict the caller to the address that fits the criteria.

The table below displays the various criteria configurations:

|            criterion           | pull w/ any address | pull restricted to address |
|:------------------------------:|:-------------------:|:--------------------------:|
|            _address_           |         OK*         |            OK**            |
| _holds non-transferable token_ |         OK*         |            OK**            |
|   _holds transferable token_   |          OK         |             OK             |

##### OK*: Pull with any address

If the airdrop is by the same dapp, then the 1DK model poses no difficulties
(eg. users who used `trade.dapp.com` can claim airdrop on `claim.dapp.com`).

If a user is eligible to claim an airdrop of `new-dapp.com` based on their usage
of `og-dapp.com` and the airdrop contract of `new-dapp.com` doesn't restrict the
message sender to be the same address that is eligible for the airdrop then the
user has the following options:

1. The user may transfer funds from the address associated with `og-dapp.com` to
a different address and [change the dapp identifier](#changing-dapp-for-address)
to `new-dapp.com`.
1. If the front end on `new-dapp.com` supports specifying a claimant address
manually (as opposed to taking the connected address as the claimant), then the
user can simply enter their address for `og-dapp.com` and pay the fees with
their key for `new-dapp.com`.
1. If the front end doesn't support it, the user can go to Etherscan or
equivalent and call the contract manually.

We note that it seems to be common practice, at least in the EVM ecosystem, not
to restrict the claimant to the message sender as evidenced by the
[Uniswap airdrop contract](https://github.com/Uniswap/merkle-distributor/blob/c3255bfa2b684594ecd562cacd7664b0f18330bf/contracts/MerkleDistributor.sol#L34)
which is often used as a model for others.  There is also no security reason to
restrict the claimant to the message sender.

The same applies if the criterion is not an address, but a non-transferable token.

##### OK**: Pull restricted to address

If the smart contract transaction to receive the airdrop can only be initiated
from the qualified address, then the user can create an empty address for the
sign up and assign the mint dapp to it later or [change the dapp
identifier](#Changing-Dapp-for-Address) of an existing address to claim the
airdrop.  Such restrictions are common for NFT-mints where users have to apply
to be placed on an allow list before the mint based on some off-chain criteria.

##### OK: Holds transferable token

Transferable tokens can be transferred through the app's native UI to any
address, therefore the user can simply transfer them to the dapp address with
which they wish to claim the token in order to become eligible.
We've only seen this requirement in scams and the act of having to transfer
an asset to a specific dapp gives warning to users.

## Q&A

#### How does the 1DK model protect from phishing with fraudulent dapps?

Here is a concrete example:

1. A user receives an urgent message notifying them of a highly sought after
   mint opportunity at a slightly misspelled domain like
   `boredapeyahtclub.com`.
1. The user opens the website, connects the wallet and approves a transaction
   which they believe will perform the mint.
1. Instead, `boredapeyahtclub.com` tries to transfer the user's NFTs to the
   attacker's address.
1. Since the user approved the malicious transaction using an address created
   specifically for `boredapeyahtclub.com` (that doesn't hold NFTs), the attack
   fails.

In general, any malicious dapp created for phishing purposes can only steal data
explicitly transferred by the user to said dapp.

#### Isn't having to send coins for transaction fees to many addresses going to be expensive?

Depends on the blockchain.  On chains like Solana with negligible transaction
fees this is not an issue.  However, on Ethereum L1 transaction fees would be
prohibitive and SealVault doesn't support ETH L1 dapps for this reason currently.

#### Isn't having to send coins for transaction fees to many addresses going to be annoying?

This is a UX issue under the control of the app.  SealVault strives to make this
convenient and we're working on automation features to make this convenient.

#### Can't two front ends hosted on different domains call the same contract?

Yes, but transactions cannot be approved with the same key for dapps on both
domains in the 1DK model.

#### What about off-chain signatures?

The 1DK model's goal is to prevent fraudulent transactions so off-chain
signatures are out scope and not restricted by the 1DK model.  See our [privacy
model](./privacy-model.md) for SealVault restrictions on off-chain signatures.

#### Isn't the 1DK model going to kill composability?

No. Following the principle of least privilege, a dapp should only need an
off-chain signatures to prove ownership of data from an other dapp. [Off-chain
signatures](#what-about-off-chain-signatures) are not restricted by the 1DK
model.

See the [Airdrops](#airdrops) section for more info on current composability
patterns.

#### Can non-transferable tokens be used with multiple dapps?

If dapp `foo.com` creates a non-transferable token and a different dapp,
`bar.com` decided to grant privileges based on whether the non-transferable
token belongs to the address used for `bar.com`, that's not going to work in the
1DK model.  However, if `bar.com` accepts an off-chain signature where the
`foo.com` address holding the non-transferable token delegates its privileges
to the `bar.com` address, that is compatible with the 1DK model.

#### Is it possible to have multiple keys per dapp?

Yes. This is a privacy question detailed in our [privacy model.](./privacy-model.md)

#### What if a hosting provider that dapps use for their front end is not added to the public suffix list?

That is a security vulnerability of the hosting provider.  The 1DK model
mitigates hosting provider vulnerabilities by limiting the effect to dapps using
said provider.

#### What if a hosting provider wants to use a domain in the public suffix list to host their own dapp?

We disallow that. A domain in the public suffix list shouldn't host anything.

#### What if a domain that was initially used for one dapp is added to the public suffix list later?

In this case the dapp becomes invalid and users have to manually transfer
transferable tokens to a new dapp identified by the new registrable domain of
the previous `suffix.tld` dapp.

#### What if a suffix is removed from the public suffix list?

We maintain our own append only version of the [public suffix
list](https://publicsuffix.org/list/public_suffix_list.dat) to prevent sharing
keys for dapps that used to resolve to different registrable domains.



## Related Standards

- [Same-Site Cookies](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Set-Cookie/SameSite)
- [Webauthn](https://developer.mozilla.org/en-US/docs/Web/API/Web_Authentication_API)
- [Dfinity Webauthn](https://medium.com/dfinity/web-authentication-and-identity-on-the-internet-computer-a9bd5754c547)
- [Solana Mobile Wallet Spec](https://solana-mobile.github.io/mobile-wallet-adapter/spec/spec.html)
