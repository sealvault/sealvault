## Overview

Dapp keys are a novel isolation mechanism for Web3 clients.  As the name
suggests, with dapp keys **one key is only allowed to approve transactions for
one dapp** without restrictions. This isolation enables automatic signature
approval and mitigates damage from compromised dapps. Data portability is
supported in [cross-connect](./cross-connect.md) mode.

## What Is a Dapp?

A dapp is a website that interacts with blockchain smart contracts through its
front end code.  A dapp is identified by its [registrable
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
dapps displayed in embedded browsing contexts.

For example, the decentralized asset management platform,
[dHEDGE](https://www.dhedge.org/) embeds other dapps like
[Aave](https://aave.com/) and [Uniswap](https://uniswap.org/) on
`app.dhedge.org`.  In the dapp key model, the identifier for both the dHEDGE and
the embedded Aave and Uniswap dapps would be `dhedge.org`.  This means that the
key used for `dhedge.org` could be used to approve transactions for the dHEDGE
dapp accessible on `app.dhedge.org`, and the Aave and the Uniswap dapps
*embedded* on `app.dhedge.org`, but the same key couldn't be used to approve
transactions when the user directly visits `app.aave.com` or `app.uniswap.org`.

Preventing the use of keys associated with embedded contexts when visiting them
directly ensures that removing an embedded dapp from a site removes its access
to other dapps on that site.

## Automatic Signature Approval

When the in-page provider connects a dapp with its own dapp key, the in-page
provider can automatically approve signature requests, since the dapp only has
access to assets the user explicitly trusted it with by transferring them to the
dapp key address.

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

## Q&A

#### Aren't dapp keys going to kill composability?

No, they won't. See the [data
portability](./in-page-provider.md#data-portability) section of the in-page
provider document for more info.

#### Isn't having to send coins for transaction fees to many addresses going to be expensive?

Depends on the blockchain.  On chains like Polygon PoS and Solana with
negligible transaction fees this is not an issue.  On Ethereum L1 transaction
fees could be prohibitive and users will use [cross-connect](./cross-connect.md)
more.

#### Isn't having to send coins for transaction fees to many addresses going to be annoying?

This is a UX issue under the control of the app.  We automate gas top-ups to
make this convenient.

#### Can't two front ends hosted on different domains call the same contract?

Yes, but transactions cannot be approved with the same key for dapps on both
domains in the dapp key model.

#### Can non-transferable tokens be used with multiple dapps?

Yes, with [cross-connect](./cross-connect.md).

#### Is it possible to have multiple keys per dapp?

Yes. This is a privacy question detailed in our [privacy model.](./privacy-model.md)

#### What if a hosting provider that dapps use for their front end is not added to the public suffix list?

That is a security vulnerability of the hosting provider.  Dapp keys
mitigate hosting provider vulnerabilities by limiting the effect to dapps using
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
   