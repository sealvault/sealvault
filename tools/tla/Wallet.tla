------------------------------- MODULE Wallet -------------------------------

EXTENDS FiniteSets, Integers, Sequences, TLC

-----------------------------------------------------------------------------

CONSTANT
    TOKENS,
    ADDRESSES,
    WEBSITES,
    TOKEN_MAPPING,
    RELAYER_MAPPING,
    WEBSITE_MAPPING,
    MAX_SIGNATURES,
    MAX_RELAYS

ASSUME TOKENS # {}
ASSUME ADDRESSES # {}
ASSUME WEBSITES # {}
ASSUME MAX_SIGNATURES > 0
ASSUME MAX_RELAYS > 0

VARIABLES
    (***********************************************************************)
    (* The set of signatures performed by the address owners.              *)
    (***********************************************************************)
    signatures,
    (***********************************************************************)
    (* Account nonces for each address.                                    *)
    (***********************************************************************)
    nonces,
    (***********************************************************************)
    (* An abstract token type where each token is unique and may only have *)
    (* one owner.                                                          *)
    (***********************************************************************)
    tokenBalances,
    (***********************************************************************)
    (* A token owner may provide authorization for another address to      *)
    (* spend the token.                                                    *)
    (***********************************************************************)
    spenderApprovals,
    (***********************************************************************)
    (* The number of relay messages.  Required to keep the model bounded.  *)
    (***********************************************************************)
    relayCount

vars == << signatures, nonces, tokenBalances, spenderApprovals, relayCount >>
-----------------------------------------------------------------------------

TokenBalancesAreDisjoint == \A a1, a2 \in ADDRESSES: a1 = a2 \/ tokenBalances[a1] \intersect tokenBalances[a2] = {}
AllTokensAreOwned == \A t \in TOKENS: \E a \in ADDRESSES: t \in tokenBalances[a]

TokenOwner(token) == CHOOSE a \in ADDRESSES: token \in tokenBalances[a]

(***************************************************************************)
(* Each token is meant to be used by its owner on certain websites.  E.g.  *)
(* the native token and USD stable coins are probably used on all          *)
(* websites.  A social NFT may be used on certain social sites.  A gaming  *)
(* NFT may be used on the game website and on an NFT marketplace.  Certain *)
(* fungible tokens may be used on a variety of exchanges.                  *)
(***************************************************************************)
DappsToTokens == [t \in TOKENS |-> WEBSITE_MAPPING[t]]

DappTokensAreNotDisjoint == \E t1, t2 \in TOKENS: DappsToTokens[t1] \intersect DappsToTokens[t2] # {}
DappTokensMayBelongToMultipleWebsites == \E t \in TOKENS: Cardinality(DappsToTokens[t]) > 1

(***************************************************************************)
(* A token implementation may trust an address to relay token transfer     *)
(* orders for tokens not owned by that address.                            *)
(***************************************************************************)
TrustedRelayers == [t \in TOKENS |-> RELAYER_MAPPING[t]]

ThereIsATrustedRelayer == \E t \in TOKENS: TrustedRelayers[t] # {}


(***************************************************************************)
(* The initial state for the state machine.                                *)
(***************************************************************************)
Init ==
  /\ signatures = { }
  /\ nonces = [a \in ADDRESSES |-> 0]
  /\ tokenBalances = [a \in ADDRESSES |-> TOKEN_MAPPING[a]]
  /\ spenderApprovals = [t \in TOKENS |-> {}]
  /\ relayCount = 0

TypeOK ==
  /\ TokenBalancesAreDisjoint
  /\ AllTokensAreOwned
  /\ DappTokensAreNotDisjoint
  /\ DappTokensMayBelongToMultipleWebsites
  /\ ThereIsATrustedRelayer

-----------------------------------------------------------------------------
(***************************************************************************)
(* Check that there is an "approval" or "transfer" type signature.         *)
(***************************************************************************)
HasValidSignature(type, address) ==
    LET sigs == {s \in signatures: /\ s.type = type
                                   /\ s.address = address
                                   /\ s.nonce = nonces[address]}
    IN /\ Cardinality(sigs) = 1

(***************************************************************************)
(* Transfer a token without checking preconditions.  Callers are expected  *)
(* to check them.                                                          *)
(***************************************************************************)
UncheckedTransfer(from, to, token) ==
    /\ tokenBalances'= [tokenBalances EXCEPT ![from] = @ \ { token },
                                             ![to] = @ \union { token }]
    /\ spenderApprovals' = [spenderApprovals EXCEPT ![token] = { }]

(***************************************************************************)
(* Transfer a token from its owner to another address.                     *)
(***************************************************************************)
Transfer(from, to, token) ==
    /\ from # to
    /\ HasValidSignature("transfer", from)
    /\ token \in tokenBalances[from]
    /\ UncheckedTransfer(from, to, token)
    /\ nonces' = [nonces EXCEPT ![from] = @ + 1]
    /\ UNCHANGED signatures
    /\ UNCHANGED relayCount

(***************************************************************************)
(* Grant authorization by the owner to another address to transfer the     *)
(* token.                                                                  *)
(***************************************************************************)
Approve(owner, spender, token) ==
    /\ owner # spender
    /\ HasValidSignature("approval", owner)
    /\ token \in tokenBalances[owner]
    /\ spenderApprovals' = [spenderApprovals EXCEPT ![token] = @ \union { spender }]
    /\ nonces' = [nonces EXCEPT ![owner] = @ + 1]
    /\ UNCHANGED signatures
    /\ UNCHANGED tokenBalances
    /\ UNCHANGED relayCount

(***************************************************************************)
(* Transfer the token initiated by an authorized address.                  *)
(***************************************************************************)
Spend(spender, recepient, token) ==
   LET owner == TokenOwner(token)
   IN /\ spender \in spenderApprovals[token]
      /\ UncheckedTransfer(owner, recepient, token)
      /\ UNCHANGED signatures
      /\ UNCHANGED nonces
      /\ UNCHANGED relayCount

(***************************************************************************)
(* Relay a token transfer order.                                           *)
(***************************************************************************)
Relay(relayer, recepient, token) ==
   LET owner == TokenOwner(token)
   IN /\ relayCount <= MAX_RELAYS
      /\ relayer \in TrustedRelayers[token]
      /\ UncheckedTransfer(owner, recepient, token)
      /\ relayCount' = relayCount + 1
      /\ UNCHANGED signatures
      /\ UNCHANGED nonces
      /\ UNCHANGED tokenBalances
      /\ UNCHANGED spenderApprovals

(***************************************************************************)
(* The owner of the address signs an "approval" or "transfer" type         *)
(* transaction.                                                            *)
(***************************************************************************)
Sign(type, address, website, token) ==
    /\ Cardinality(signatures) <= MAX_SIGNATURES
    /\ signatures' = signatures \union {[type |-> type,
                                         address |-> address,
                                         website |-> website,
                                         token |-> token,
                                         nonce |-> nonces[address]]}
    /\ UNCHANGED nonces
    /\ UNCHANGED tokenBalances
    /\ UNCHANGED spenderApprovals
    /\ UNCHANGED relayCount

(***************************************************************************)
(* The step in the state machine.                                          *)
(***************************************************************************)
Next ==
    \/ \E owner \in ADDRESSES, website \in WEBSITES, token \in TOKENS, type \in {"transfer", "approval"}:
        Sign(type, owner, website, token)
    \/ \E owner, to \in ADDRESSES, token \in TOKENS:
        \/ Transfer(owner, to, token)
        \/ Approve(owner, to, token)
    \/ \E spender, to \in ADDRESSES, token \in TOKENS:
        Spend(spender, to, token)
    \/ \E to \in ADDRESSES, token \in TOKENS: \E relayer \in TrustedRelayers[token]:
        Relay(relayer, to, token)

Spec == Init /\ [][Next]_vars

=============================================================================

