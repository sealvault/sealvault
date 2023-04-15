---
slug: 2023/04/token-transfer-tla
date: 2023-04-14
authors:
  - agostbiro

links:
  - dev-docs/design/dapp-keys.md
  - dev-docs/design/cross-connect.md
  - dev-docs/design/token-transfer-traces.md
---

# Exploring Ethereum Token Transfers with TLA+ for Wallet Security


 _TLDR: Formal methods facilitate thinking in a rigorous way about the problem
 and help catch errors even if we don’t use them to verify the implementation._

<!-- more -->

At SealVault, we’re trying to build solutions where we can make security
guarantees to users. This gives users peace of mind and improves UX since it
lets us automate things and get rid of confusing warnings.

Connecting an Ethereum address to multiple dapps is common practice in wallet
applications, but it’s very difficult to make security guarantees in this
setting. Wallets typically make no guarantees and rely on the user’s judgement
to secure her assets.

The first step towards building a better solution is to understand what can go
wrong. The most common thing that [goes
wrong](/dev-docs/design/attack-tree/#approval-spoofing) when the same Ethereum
address is connected to multiple dapps is that a malicious or compromised dapp
transfers the user’s tokens without their consent. The user is a victim of
fraud, but the transaction that transfers the tokens is valid per the Ethereum
protocol. So in order to prevent fraud, we have to understand how valid
transactions can occur.

There is only one way a native token can be transferred from an EOA ignoring gas
fees (namely the user signs a transaction authorizing the transfer). There are
many different ways custom tokens can be transferred though with a combination
of spender approvals and meta transactions. I initially collected 13 different
ways a custom token can be transferred and [visualized
it](/dev-docs/design/token-transfer-traces/#custom-token-transfer) using
diagrams. Diagrams explain well how a given a solution works, but it’s difficult
to know if they give a complete picture of the system. This is why I turned to
TLA+.

TLA+ is a minimal language to specify system designs with mathematical formulas.
A TLA+ specification is a declarative statement of what can happen in a system
using logic and set operators. TLA+ also comes with a model checker called TLC
that generates system behaviors based on the specification and checks that the
possible behaviors satisfy certain formulas. While TLA+ is a general purpose
specification language, it is most commonly used to specify distributed systems.
In fact, it was when I realized that securing Ethereum token transfers in a
wallet application is a distributed systems problem that I turned to TLA+.

The parties to a custom token transfer from a dapp are the following:

- the wallet application,
- the dapp application, 
- Ethereum nodes,
- relayer nodes that submit messages signed by the user to smart contracts to save gas fees for the user. 

As wallet implementors, we can assume that the Ethereum protocol functions
correctly, but we can’t make any assumptions about the behavior of dapps and
relayers. We also cannot make assumptions about message delivery or assume that
if a transaction was submitted, it’ll be carried out.

Our TLA+ spec abstracts away 

- different custom token types
([ERC-20](https://eips.ethereum.org/EIPS/eip-20),
[ERC-721](https://eips.ethereum.org/EIPS/eip-721),
[ERC-1155](https://eips.ethereum.org/EIPS/eip-1155)), 
- where transactions originate from,
- how transactions are delivered to nodes.

The spec is only concerned with transaction types, who the signer is and whether
a transaction occurred after a valid transaction was submitted. Whether a
transaction occurred is modeled with events.

There are five basic types of transactions that can lead to custom token
transfers:

1. Standard `transfer` method calls,
1. Standard `approve` method calls,
1. [ERC-2612
   Permit](/dev-docs/design/token-transfer-traces/#permit)
   transactions,
1. [Permit2](/dev-docs/design/token-transfer-traces/#permit2)
transactions, 
1. and most importantly a transaction that calls an unknown method of an unknown
   contract.

An unknown transaction call can lead to a token transfer if a contract was
approved as spender for the token. Each transaction type also has a
corresponding [meta
transaction](/dev-docs/design/token-transfer-traces/#meta-transaction) when the
transaction is submitted by a relayer, so that makes ten types of transactions
in total. Signers can be the token owner, an approved spender EOA or any
address. Any address can be the signer to transfer a token if a contract address
was approved as spender for the token.

The valid actions in the system are specified as either submitting a transaction
or emitting a token approval or a token transfer event:

```tla+
Next ==
    \* Transactions
    \/ \E s \in Signer:
        \/ Transfer(s)
        \/ Approve(s)
        \/ Permit(s)
        \/ Permit2(s)
        \/ UnknownTransaction(s)
        \/ MetaTransfer(s)
        \/ MetaApprove(s)
        \/ MetaPermit(s)
        \/ MetaPermit2(s)
        \/ MetaUnknownTransaction(s)
    \* Events
    \/ TokenApproval
    \/ TokenTransfer
```

A token approval event can be emitted only if the owner signed an approval or
permit transaction (or the corresponding meta-transaction):

```tla+
TokenApproval ==
   /\ ~ "TokenApproval" \in events
   /\ ApprovedToken
   /\ events' = events \union {"TokenApproval"}
   /\ UNCHANGED transactions

ApprovedToken ==
    \/ TransactionExists("approve", "owner")
    \/ TransactionExists("meta-approve", "owner")
    \/ TransactionExists("permit", "owner")
    \/ TransactionExists("meta-permit", "owner")
```

A token transfer event can be emitted only if the owner or an approved spender
transferred the token:

```tla+
TokenTransfer ==
    /\ ~ TokenWasTransferred
    /\
        \/ OwnerTransferToken
        \/ SpendWithApproval
    /\ UNCHANGED transactions
```

The owner can transfer the token either with a normal or a meta transaction:

```tla+
OwnerTransferToken ==
    /\
        \/ TransactionExists("transfer", "owner")
        \/ TransactionExists("meta-transfer", "owner")
    /\ events' = events \union {"TokenTransferOwner"}
```

An approved spender can transfer the token in a variety of ways. If the spender
is an EOA, then the spender must have signed a normal or a meta transfer.
But if the spender is a contract, then any contract method call can lead to a
transfer and there is no guarantee, that the originator of the transaction is
the owner:

```tla+
SpendWithApproval ==
    /\ "TokenApproval" \in events
    /\ SpendToken
    /\ events' = events \union {"TokenTransferSpender"}

SpendToken ==
    \/ TransactionExists("transfer", "spender")
    \/ TransactionExists("meta-transfer", "spender")
    \/ TransactionExists("unknown-transaction", "owner")
    \/ TransactionExists("unknown-transaction", "any")
    \/ TransactionExists("meta-unknown-transaction", "owner")
    \/ TransactionExists("meta-unknown-transaction", "any")
    \/ TransactionExists("permit2", "owner")
    \/ TransactionExists("permit2", "any")
    \/ TransactionExists("meta-permit2", "owner")
    \/ TransactionExists("meta-permit2", "any")
```

Looking at the structure of the specification, it's obvious that my initial
[diagrams](/dev-docs/design/token-transfer-traces) that documented 13 ways a custom token can be transferred severely
underestimated the complexity of the problem. There are 2 ways the owner can
transfer the tokens, there are 4 ways a spender can be approved and there are 10
ways spenders can transfer tokens, so that means there are $2 + 4 * 10 =
42$ ways a custom token can be transferred from an EOA.

The entire specification with invariants and temporal properties that codify our
assumptions is available on [GitHub.](https://github.com/sealvault/sealvault/blob/main/tools/tla/TokenTransfer.tla)

So what did we achieve by specifying Ethereum token transfers from a wallet
perspective with TLA+?

1. We have discovered that I have initially severely underestimated the
   complexity of the problem.
1. It facilitated a more rigorous way of thinking about the problem and deepened
   our understanding of the problem space.
1. We have made our assumptions explicit, and stated them precisely.
1. We now have a formal specification of Ethereum token transfers against which
   we can test later assumptions or solutions that arise through the development
   process.