------------------------------- MODULE TokenTransfer ------------------------------

\* The spec abstracts away different custom token types where transactions
\* originate from and how they’re delivered to nodes. It’s only concerned with
\* transaction types, who the signer is and whether a transaction occurred after a
\* valid transaction was submitted. Whether a transaction occurred is modeled with
\* events. Gas fees are not modeled.
\* See https://sealvault.org/dev-docs/design/token-transfer-traces/ for a
\* detailed explanation of the various transaction patterns.

EXTENDS FiniteSets, Sequences

VARIABLES
    \* The set of events produced by Ethereum nodes. See `Event` for details.
    events,
    \* The set of transactions signed by the token owner. See `Transaction` for details.
    transactions

vars == << events, transactions >>

TransactionType == {
    \* IERC20 transfer call.
    "transfer",
    \* IERC20 approve call.
    "approve",
    \* ERC-2612 transaction
    "permit",
    \* Permit2 pattern transaction
    "permit2",
    \* Call a contract method that is not part of IERC20.
    "unknown-transaction",

    \* The following are meta transactions. Meta transactions are signed with an
    \* off-chain signature (typically EIP-712), and then relayed by another party
    \* to Ethereum nodes. The relayer pays gas fees.
    \* Note that the spec assumes that only meta transactions with valid signatures are relayed.
    \* While this seems to be how relayers work in practice, it's not required
    \* by any standard that the author knows of.

    \* IERC20 transfer call with a meta transaction.
    "meta-transfer",
    \* IERC20 approve call with a meta transaction.
    "meta-approve",
    \* ERC-2612 transaction submitted by a relayer
    "meta-permit",
    \* Permit2 pattern transaction submitted by a relayer
    "meta-permit2",
    \* Call a method that is not part of IERC20 with a meta transaction.
    "meta-unknown-transaction"
}

\* The signer of the transaction or the meta transaction.
\* The owner is the token owner address.
\* The spender is the approved spender address in the ERC-20 sense.
\* Any means any address.
Signer == {"owner", "spender", "any"}

Event == {
    \* The token was transferred by the owner.
    "TokenTransferOwner",
    \* The token was transferred by the approved spender.
    "TokenTransferSpender",
    \* The token was approved by the owner.
    "TokenApproval"
}

Transaction == [type: TransactionType, signer: Signer]

TypeOK ==
    /\ events \subseteq Event
    \* Sanity check for the spec: the token can be only transferred once.
    /\ ~ {"TokenTransferOwner", "TokenTransferSpender"} \subseteq events
    /\ transactions \subseteq Transaction

Init ==
    /\ events = { }
    /\ transactions = { }

\* Transactions

TransactionExists(type, signer) ==
    /\ \E t \in transactions: t.type = type /\ t.signer = signer

SendTransactionOnce(tx) ==
    \* Restrict to one transaction always to keep the state space small. In
    \* practice there might be multiple transactions, eg. if one gets stuck in the
    \* mem pool and a new one is sent with higher gas allowance to replace it.
    /\ ~ TransactionExists(tx.type, tx.signer)
    /\ transactions' = transactions \union {tx}

Transfer(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "transfer", signer |-> signer])
    /\ UNCHANGED events

Approve(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "approve", signer |-> signer])
    /\ UNCHANGED events

UnknownTransaction(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "unknown-transaction", signer |-> signer])
    /\ UNCHANGED events

Permit(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "permit", signer |-> signer])
    /\ UNCHANGED events

Permit2(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "permit2", signer |-> signer])
    /\ UNCHANGED events

MetaTransfer(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "meta-transfer", signer |-> signer])
    /\ UNCHANGED events

MetaApprove(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "meta-approve", signer |-> signer])
    /\ UNCHANGED events

MetaUnknownTransaction(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "meta-unknown-transaction", signer |-> signer])
    /\ UNCHANGED events

MetaPermit(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "meta-permit", signer |-> signer])
    /\ UNCHANGED events

MetaPermit2(signer) ==
    /\ ~ "TokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "meta-permit2", signer |-> signer])
    /\ UNCHANGED events

\* Events

ApprovedToken ==
    \/ TransactionExists("approve", "owner")
    \/ TransactionExists("meta-approve", "owner")
    \/ TransactionExists("permit", "owner")
    \/ TransactionExists("meta-permit", "owner")

TokenApproval ==
    /\ ~ "TokenApproval" \in events
    /\ ApprovedToken
    /\ events' = events \union {"TokenApproval"}
    /\ UNCHANGED transactions

OwnerTransferToken ==
    /\
        \/ TransactionExists("transfer", "owner")
        \/ TransactionExists("meta-transfer", "owner")
    /\ events' = events \union {"TokenTransferOwner"}

SpendToken ==
    \/ TransactionExists("transfer", "spender")
    \/ TransactionExists("meta-transfer", "spender")
    \* If the approved spender is a contract, then any contract
    \* method call can lead to a transfer and there is no guarantee,
    \* that the originator of the transaction is the owner.
    \/ TransactionExists("unknown-transaction", "owner")
    \/ TransactionExists("unknown-transaction", "any")
    \/ TransactionExists("meta-unknown-transaction", "owner")
    \/ TransactionExists("meta-unknown-transaction", "any")
    \/ TransactionExists("permit2", "owner")
    \/ TransactionExists("permit2", "any")
    \/ TransactionExists("meta-permit2", "owner")
    \/ TransactionExists("meta-permit2", "any")

SpendWithApproval ==
    /\ "TokenApproval" \in events
    /\ SpendToken
    /\ events' = events \union {"TokenTransferSpender"}

TokenWasTransferred ==
    {"TokenTransferOwner", "TokenTransferSpender"} \intersect events # { }

TokenTransfer ==
    /\ ~ TokenWasTransferred
    /\
        \/ OwnerTransferToken
        \/ SpendWithApproval
    /\ UNCHANGED transactions

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

Spec ==
    /\ Init
    /\ [][Next]_vars

\* A token can be only transferred if a transaction was signed by the owner.
TransferRequiresOwnerSig ==
    TokenWasTransferred => \E t \in transactions: t.signer = "owner"

\* If there was no token approval, then the owner must have signed a transfer
\* transaction to transfer a token.
WithoutApprovalOnlyTransfer ==
    (TokenWasTransferred /\ ~ "TokenApproval" \in events) =>
        \E t \in transactions:
            t.signer = "owner" /\ t.type \in {"transfer", "meta-transfer"}

\* Asserts that these invariants hold at every execution step.
Invariants ==
    /\ TypeOK
    /\ TransferRequiresOwnerSig
    /\ WithoutApprovalOnlyTransfer

\* Asserts that there is no weak fairness in the system. Just because a
\* transaction was submitted to the mempool, doesn't guarantee that it happens.
\* Similarly, just because meta transaction was submitted to a relayer, doesn't
\* mean that it'll be carried out.
TemporalProperties ==
    \* If a token transfer by the owner is possible, doesn't guarantee that it happens.
    /\ <>[](ENABLED <<OwnerTransferToken>>_events) => ~ []<><<OwnerTransferToken>>_events
    \* If a token approval is possible, doesn't guarantee that it happens.
    /\ <>[](ENABLED <<TokenApproval>>_events) => ~ []<><<TokenApproval>>_events
    \* If a token was approved, doesn't guarantee that the approvee will spend it.
    /\ <>[](ENABLED <<SpendWithApproval>>_events) => ~ []<><<SpendWithApproval>>_events

=============================================================================