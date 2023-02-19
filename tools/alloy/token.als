sig Token {}
sig FungibleToken extends Token {}
sig NativeToken extends FungibleToken {}
sig CustomToken extends FungibleToken {}
sig NonFungibleToken extends Token {
	balances:  Address -> lone NonFungibleTokenId
}
sig NonFungibleTokenId {}

sig Address {}

assert Wrong {
  all nft: NonFungibleToken, nftId: NonFungibleTokenId | one a: Address | nftId in nft.balances[a]
}

check Wrong
