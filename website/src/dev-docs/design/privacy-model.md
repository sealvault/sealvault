# Privacy Model

Blockchain transactions are pseudonymous, ergo the strongest privacy model we
can support is pseudonymity.  The pseudonym is the address derived from the
public key. SealVault never shares users' pseudonyms with anyone.

Multiple pseudonyms of a user may be tied together by observing transaction
patterns between addresses or based on IP addresses.  Correlation based on
transactions is permanent by default and observable by anybody.  Correlation
based on IP addresses may be permanent, but only available to blockchain API
providers.

## Profile

The privacy boundary in SealVault is the profile.  A profile is a collection of
addresses.  A profile can contain addresses from multiple chains, because
cross-chain bridging may correlate addresses from different chains.

Users can only send tokens between addresses in the same profile within
SealVault.  While the [1DK](./one-dapp-per-key.md) model prevents producing
transactions with an address for multiple dapps, users may produce off-chain
signatures for multiple dapps in the same profile.  In the future, users will be
able to prove claims between profiles with zero-knowledge proofs without
correlating addresses between different profiles.

Users may correlate addresses in different profiles outside of
SealVault.  We can't prevent this, but we warn users against it. We also can't
prevent correlating addresses based on IP addresses.

Profiles may be merged, but they may not be split.



