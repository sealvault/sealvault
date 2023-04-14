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
    "transfer-custom",
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
    "meta-transfer-custom",
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
    "CustomTokenTransfer",
    \* IERC20 Approval event.
    "CustomTokenApproval"
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

TransferCustom(signer) ==
    /\ ~ "CustomTokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "transfer-custom", signer |-> signer])
    /\ UNCHANGED events

ApproveCustom(signer) ==
    /\ ~ "CustomTokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "approve", signer |-> signer])
    /\ UNCHANGED events

UnknownTransaction(signer) ==
    /\ ~ "CustomTokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "unknown-transaction", signer |-> signer])
    /\ UNCHANGED events

MetaTransferCustom(signer) ==
    /\ ~ "CustomTokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "meta-transfer-custom", signer |-> signer])
    /\ UNCHANGED events

MetaApproveCustom(signer) ==
    /\ ~ "CustomTokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "meta-approve", signer |-> signer])
    /\ UNCHANGED events

MetaUnknownTransaction(signer) ==
    /\ ~ "CustomTokenTransfer" \in events
    /\ SendTransactionOnce([type |-> "meta-unknown-transaction", signer |-> signer])
    /\ UNCHANGED events

\* Events

CustomTokenApproval ==
    /\ ~ "CustomTokenApproval" \in events
    /\
        \/ TransactionExists("approve", "owner")
        \/ TransactionExists("meta-approve", "owner")
    /\ events' = events \union {"CustomTokenApproval"}
    /\ UNCHANGED transactions

CustomTokenTransfer ==
    /\ ~ "CustomTokenTransfer" \in events
    /\
        \/ TransactionExists("transfer-custom", "owner")
        \/ TransactionExists("meta-transfer-custom", "owner")
        \/
            /\ "CustomTokenApproval" \in events
            /\
                \/ TransactionExists("transfer-custom", "spender")
                \/ TransactionExists("meta-transfer-custom", "spender")
                \* If the approved spender is a contract, then any contract
                \* method call can lead to a transfer and there is no guarantee,
                \* that the originator of the transaction is the owner.
                \/ TransactionExists("unknown-transaction", "owner")
                \/ TransactionExists("unknown-transaction", "any")
                \/ TransactionExists("meta-unknown-transaction", "owner")
                \/ TransactionExists("meta-unknown-transaction", "any")
    /\ events' = events \union {"CustomTokenTransfer"}
    /\ UNCHANGED transactions

Next ==
    \* Transactions
    \/ \E s \in Signer:
        \/ TransferCustom(s)
        \/ ApproveCustom(s)
        \/ UnknownTransaction(s)
        \/ MetaTransferCustom(s)
        \/ MetaApproveCustom(s)
        \/ MetaUnknownTransaction(s)
    \* Events
    \/ CustomTokenApproval
    \/ CustomTokenTransfer

Spec == 
    /\ Init 
    /\ [][Next]_vars 

\* A token can be only transferred if a transaction was signed by the owner.
TransferRequiresOwnerSig ==
    "CustomTokenTransfer" \in events => \E t \in transactions: t.signer = "owner"

\* If there was no token approval, then the owner must have signed a transfer transaction to transfer a token.
WithoutApprovalOnlyTransfer ==
    ("CustomTokenTransfer" \in events /\ ~ "CustomTokenApproval" \in events) => 
        \E t \in transactions: 
            t.signer = "owner" /\ t.type \in {"transfer-custom", "meta-transfer-custom"}

Invariants ==
    /\ TypeOK
    /\ TransferRequiresOwnerSig
    /\ WithoutApprovalOnlyTransfer

TemporalProperties ==
    \* Neither event is guaranteed to happen if enabling conditions are always on
    \* due to stuttering steps. In other words, there is no (weak) fairness in the system.
    /\ <>[](ENABLED <<CustomTokenTransfer>>_events) => ~ []<><<CustomTokenTransfer>>_events
    /\ <>[](ENABLED <<CustomTokenApproval>>_events) => ~ []<><<CustomTokenTransfer>>_events

=============================================================================