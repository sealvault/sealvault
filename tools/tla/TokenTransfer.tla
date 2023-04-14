------------------------------- MODULE TokenTransfer ------------------------------

\* Gas fees are not modeled.

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
    \* Call a method that is not part of IERC20 with a meta transaction.
    "meta-unknown-transaction"
}

\* The signer of the transaction or the meta transaction.
\* The owner is the token owner address.
\* The spender is the approved spender address in the ERC-20 sense.
\* Any means any address.
Signer == {"owner", "spender", "any"}

Event == {
    \* IERC20 Transfer event.
    "TokenTransfer",
    \* IERC20 Approval event.
    "TokenApproval"
}

Transaction == [type: TransactionType, signer: Signer]

TypeOK ==
    /\ events \subseteq Event
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

\* Events

TokenApproval ==
    /\ ~ "TokenApproval" \in events
    /\
        \/ TransactionExists("approve", "owner")
        \/ TransactionExists("meta-approve", "owner")
    /\ events' = events \union {"TokenApproval"}
    /\ UNCHANGED transactions


TokenTransfer ==
    /\ ~ "TokenTransfer" \in events
    /\
        \/ TransactionExists("transfer", "owner")
        \/ TransactionExists("meta-transfer", "owner")
        \/
            /\ "TokenApproval" \in events
            /\
                \/ TransactionExists("transfer", "spender")
                \/ TransactionExists("meta-transfer", "spender")
                \* If the approved spender is a contract, then any contract
                \* method call can lead to a transfer and there is no guarantee,
                \* that the originator of the transaction is the owner.
                \/ TransactionExists("unknown-transaction", "owner")
                \/ TransactionExists("unknown-transaction", "any")
                \/ TransactionExists("meta-unknown-transaction", "owner")
                \/ TransactionExists("meta-unknown-transaction", "any")
    /\ events' = events \union {"TokenTransfer"}
    /\ UNCHANGED transactions

Next ==
    \* Transactions
    \/ \E s \in Signer:
        \/ Transfer(s)
        \/ Approve(s)
        \/ UnknownTransaction(s)
        \/ MetaTransfer(s)
        \/ MetaApprove(s)
        \/ MetaUnknownTransaction(s)
    \* Events
    \/ TokenApproval
    \/ TokenTransfer

Spec == 
    /\ Init 
    /\ [][Next]_vars 

\* A token can be only transferred if a transaction was signed by the owner.
TransferRequiresOwnerSig ==
    "TokenTransfer" \in events => \E t \in transactions: t.signer = "owner"

\* If there was no token approval, then the owner must have signed a transfer transaction to transfer a token.
WithoutApprovalOnlyTransfer ==
    ("TokenTransfer" \in events /\ ~ "TokenApproval" \in events) => 
        \E t \in transactions: 
            t.signer = "owner" /\ t.type \in {"transfer", "meta-transfer"}

Invariants ==
    /\ TypeOK
    /\ TransferRequiresOwnerSig
    /\ WithoutApprovalOnlyTransfer

TemporalProperties ==
    \* Neither event is guaranteed to happen if enabling conditions are always on
    \* due to stuttering steps. In other words, there is no (weak) fairness in the system.
    /\ <>[](ENABLED <<TokenTransfer>>_events) => ~ []<><<TokenTransfer>>_events
    /\ <>[](ENABLED <<TokenApproval>>_events) => ~ []<><<TokenTransfer>>_events

=============================================================================