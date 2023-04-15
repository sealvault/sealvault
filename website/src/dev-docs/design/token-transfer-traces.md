# Token Transfer Traces

## Overview

This document explains the different ways a token can be transferred from an
externally owned account (EOA) with the Ethereum protocol. It is a companion to
the custom token transfer [TLA+
spec.](https://github.com/sealvault/sealvault/blob/main/tools/tla/TokenTransfer.tla)
There is also a [blog post](/blog/2023/04/token-transfer-tla) that
explains the TLA+ spec.

The document differentiates between custom and native tokens, but not between
custom tokens ([ERC-20](https://eips.ethereum.org/EIPS/eip-20),
[ERC-721](https://eips.ethereum.org/EIPS/eip-721),
[ERC-1155](https://eips.ethereum.org/EIPS/eip-1155)) and ignores the different
transfer methods of contracts. Gas fees are not modelled.

## Native Token Transfer

A native token transfer happens without contract execution. 

```mermaid
flowchart TB
    on_chain_sig[On-Chain Sig] -->  eth_nodes[ETH Nodes]
    eth_nodes --> native_token_transfer[Native Token Transfer]
```

## Custom Token Transfer

The simplest form of transferring a custom token is with a single on-chain
signature. The caller of the transfer method of the token contract must be the
token owner EOA in this case.

```mermaid
flowchart TB
    on_chain_sig[On-Chain Sig] -->  eth_nodes[ETH Nodes]
    eth_nodes -->  token_contract[Token Contract]
    token_contract --> custom_token_transfer[Custom Token Transfer]
```

## Custom Token Approval

The token owner EOA can allow an other address (EOA or contract) to spend the
token with an approval.

### EOA spender

```mermaid
flowchart TB
    on_chain_sig_approve[On-Chain Sig Approve]-->|Step 1|eth_nodes[ETH Nodes]
    eth_nodes-->token_contract[Token Contract]
    token_contract-->custom_token_approval[Custom Token Approval]
    
    on_chain_sig_transfer[On-Chain Sig Transfer]-->|Step 2|eth_nodes
    eth_nodes -->  token_contract[Token Contract]
    token_contract --> custom_token_transfer[Custom Token Transfer]
    
    %% CSS-based class defs don't work
    classDef green stroke:green;
    classDef orange stroke:orange;
    
    class on_chain_sig_approve green
    class custom_token_approval green
    linkStyle 0 stroke: green
    linkStyle 1 stroke: green
    linkStyle 2 stroke: green
    
    class on_chain_sig_transfer orange
    class custom_token_transfer orange
    linkStyle 3 stroke: orange
    linkStyle 4 stroke: orange
    linkStyle 5 stroke: orange
```

### Contract Spender

```mermaid
flowchart TB
    on_chain_sig_approve[On-Chain Sig Approve]-->|Step 1|eth_nodes[ETH Nodes]
    eth_nodes-->token_contract[Token Contract]
    token_contract-->custom_token_approval[Custom Token Approval]
    
    on_chain_sig_spend[On-Chain Sig Tx]-->|Step 2|eth_nodes
    eth_nodes-->spender_contract[Spender Contract]
    spender_contract-->token_contract
    token_contract-->custom_token_transfer[Custom Token Transfer]
    
    %% CSS-based class defs don't work
    classDef green stroke:green;
    classDef orange stroke:orange;
    
    class on_chain_sig_approve green
    class custom_token_approval green
    linkStyle 0 stroke: green
    linkStyle 1 stroke: green
    linkStyle 2 stroke: green
    
    class on_chain_sig_spend orange
    class custom_token_transfer orange
    linkStyle 3 stroke: orange
    linkStyle 4 stroke: orange
    linkStyle 5 stroke: orange
    linkStyle 6 stroke: orange
```

### Off-Chain Spend

Following an on-chain spender approval by the token owner, an off-chain
signature by the owner can suffice to execute a transfer of the token. This
pattern is typically used by exchanges and marketplaces such as [CoW
Swap](https://docs.cow.fi/) and
[Seaport.](https://docs.opensea.io/reference/seaport-overview)

```mermaid
flowchart TB
    on_chain_sig_approve[On-Chain Sig Approve]-->|Step 1|eth_nodes[ETH Nodes]
    eth_nodes-->token_contract[Token Contract]
    token_contract-->custom_token_approval[Custom Token Approval]
    
    off_chain_sig_spend[Off-Chain Sig Tx]-->|Step 2|relayer
    relayer[Relayer] --> eth_nodes
    eth_nodes-->spender_contract[Spender Contract]
    spender_contract-->token_contract
    token_contract-->custom_token_transfer[Custom Token Transfer]
    
    %% CSS-based class defs don't work
    classDef green stroke:green;
    classDef orange stroke:orange;
    
    class on_chain_sig_approve green
    class custom_token_approval green
    linkStyle 0 stroke: green
    linkStyle 1 stroke: green
    linkStyle 2 stroke: green
    
    class off_chain_sig_spend orange
    class relayer orange
    class custom_token_transfer orange
    class spender_contract orange
    linkStyle 3 stroke: orange
    linkStyle 4 stroke: orange
    linkStyle 5 stroke: orange
    linkStyle 6 stroke: orange
    linkStyle 7 stroke: orange
```

### Permit

If a token contract implements the permit extension defined in
[ERC-2612](https://eips.ethereum.org/EIPS/eip-2612), the token owner EOA can
grant a spender approval to an address (EOA or contract) with an off-chain
signature. The permit message doesn't have to be passed by the EOA to the token
contract. [More
info.](https://github.com/dragonfly-xyz/useful-solidity-patterns/tree/main/patterns/erc20-permit)

#### Permit Contract Spender

##### Permit Contract Spender Single Tx

```mermaid
flowchart TB
    off_chain_sig_permit[Off-Chain Sig Permit] -->  on_chain_sig_tx[On-Chain Sig Tx]
    on_chain_sig_tx --> eth_nodes[ETH Nodes]
    eth_nodes --> spender_contract[Spender Contract]
    spender_contract-->|Call Permit|token_contract[Token Contract]
    spender_contract-->|Call Transfer|token_contract[Token Contract]
    token_contract --> custom_token_approval[Custom Token Approval]
    token_contract --> custom_token_transfer[Custom Token Transfer]
```

##### Permit Contract Spender Multiple Tx

```mermaid
flowchart TB
    off_chain_sig_permit[Off-Chain Sig Permit]-->|Step 1|on_chain_sig_tx[On-Chain Sig Tx]
    on_chain_sig_tx --> eth_nodes[ETH Nodes]
    eth_nodes --> spender_contract[Spender Contract]
    spender_contract-->|Call Permit|token_contract[Token Contract]
    token_contract --> custom_token_approval[Custom Token Approval]
    
    on_chain_sig_spend[On-Chain Sig Spend]-->|Step 2|eth_nodes[ETH Nodes]
    eth_nodes --> spender_contract
    spender_contract -->|Call Transfer| token_contract
    token_contract --> custom_token_transfer[Custom Token Transfer]
    
    %% CSS-based class defs don't work
    classDef green stroke:green;
    classDef orange stroke:orange;
    
    class off_chain_sig_permit green
    class on_chain_sig_tx green
    class on_chain_sig_approval green
    class custom_token_approval green
    linkStyle 0 stroke: green
    linkStyle 1 stroke: green
    linkStyle 2 stroke: green
    linkStyle 3 stroke: green
    linkStyle 4 stroke: green
    
    class custom_token_transfer orange
    class on_chain_sig_spend orange
    linkStyle 5 stroke: orange
    linkStyle 6 stroke: orange
    linkStyle 7 stroke: orange
    linkStyle 8 stroke: orange
```

#### Permit EOA Spender

```mermaid
flowchart TB
    off_chain_sig_permit[Off-Chain Sig Permit]-->|Step 1|on_chain_sig_tx[On-Chain Sig Tx]
    on_chain_sig_tx-->eth_nodes[ETH Nodes]
    eth_nodes-->token_contract[Token Contract]
    token_contract-->custom_token_transfer[Custom Token Approval]
    
    on_chain_sig_transfer[Spender On-Chain Sig Transfer]-->|Step 2|eth_nodes
    eth_nodes-->token_contract
    
    token_contract --> custom_token_transfer[Custom Token Transfer]
    
    class off_chain_sig_permit green
    class on_chain_sig_tx green
    class on_chain_sig_approval green
    linkStyle 0 stroke: green
    linkStyle 1 stroke: green
    linkStyle 2 stroke: green
    linkStyle 3 stroke: green
    
    class off_chain_sig_transfer orange
    class custom_token_transfer orange
    linkStyle 4 stroke: orange
    linkStyle 5 stroke: orange
    linkStyle 6 stroke: orange
```

### Permit2

Single spender contract used by all protocols. Advantage over [ERC-20
Permit](#erc-20-permit) is that it doesn't need changes to the token contract. [More info.](https://github.com/dragonfly-xyz/useful-solidity-patterns/tree/main/patterns/permit2)


```mermaid
flowchart TB
    on_chain_sig_approve[On-Chain Sig Approve]-->|Step 1|eth_nodes[ETH Nodes]
    eth_nodes-->token_contract[Token Contract]
    token_contract-->custom_token_approval[Custom Token Approval]
    
    off_chain_sig_permit[Off-Chain Sig Permit]-->|Step 2|on_chain_sig_tx[On-Chain Sig Tx]
    on_chain_sig_tx --> eth_nodes[ETH Nodes]
    eth_nodes --> protocol_contract[Protocol Contract]
    protocol_contract --> spender_contract[Spender Contract]
    spender_contract --> token_contract
    token_contract --> custom_token_transfer[Custom Token Transfer]
    
    %% CSS-based class defs don't work
    classDef green stroke:green;
    classDef orange stroke:orange;
    
    class on_chain_sig_approve green
    class custom_token_approval green
    linkStyle 0 stroke: green
    linkStyle 1 stroke: green
    linkStyle 2 stroke: green
    
    class off_chain_sig_permit orange
    class on_chain_sig_tx orange
    class on_chain_sig_spend orange
    class custom_token_transfer orange
    class protocol_contract orange
    class spender_contract orange
    linkStyle 3 stroke: orange
    linkStyle 4 stroke: orange
    linkStyle 5 stroke: orange
    linkStyle 6 stroke: orange
    linkStyle 7 stroke: orange
    linkStyle 8 stroke: orange
```

## Meta Transaction

With meta transactions ([ERC-2771](https://eips.ethereum.org/EIPS/eip-2771)),
the token implementation trusts a forwarder contract to feed it transactions to
save gas fees for the EOA. The token contract treats method calls from the
forwarder as if they were called by the EOA directly. 

It is assumed that the forwarder contract verifies off-chain signatures by the
user, but it's not verified by the token contract. If the relayer fails to
verify the owner's signature, we treat that as a vulnerability of the token
contract, since it's the token contract that chooses to trust the relayer.

### Meta Custom Token Transfer

```mermaid
flowchart TB
    off_chain_sig[Off-Chain Sig Transfer] --> relayer[Relayer]
    relayer --> eth_nodes[ETH Nodes]
    eth_nodes --> trusted_forwarder_contract[Trusted Forwarder Contract]
    trusted_forwarder_contract --> token_contract[Token Contract]
    token_contract --> custom_token_transfer[Custom Token Transfer]
```

### Meta Custom Token Approval

#### Meta EOA spender

Token approval with meta transaction where the spender is an EOA. On the 2/A
path, the approved spender transfers the token through a meta-transaction. On
the 2/B path, the approved spender EOA transfers the token via a normal
transaction.

```mermaid
flowchart TB
    off_chain_sig[Off-Chain Sig Approve] -->|Step 1| relayer[Relayer]
    relayer --> eth_nodes[ETH Nodes]
    eth_nodes --> trusted_forwarder_contract[Trusted Forwarder Contract]
    trusted_forwarder_contract --> token_contract[Token Contract]
    token_contract --> custom_token_approval[Custom Token Approval]
    
    off_chain_sig[Off-Chain Sig] -->|Step 2/A| relayer[Relayer]
    relayer -->|2/A| eth_nodes[ETH Nodes]
    eth_nodes -->|2/A| trusted_forwarder_contract
    eth_nodes -->|2/B| token_contract[Token Contract]
    trusted_forwarder_contract -->|2/A| token_contract
    token_contract --> custom_token_transfer[Custom Token Transfer]
    
    on_chain_sig_transfer[On-Chain Sig Transfer] -->|Step 2/B| eth_nodes[ETH Nodes]
    
    %% CSS-based class defs don't work
    classDef green stroke:green;
    classDef orange stroke:orange;
    
    class on_chain_sig_approve green
    class custom_token_approval green
    class trusted_forwarder_contract green
    linkStyle 0 stroke: green
    linkStyle 1 stroke: green
    linkStyle 2 stroke: green
    linkStyle 3 stroke: green
    linkStyle 4 stroke: green
    
    class on_chain_sig_transfer orange
    class custom_token_transfer orange
    linkStyle 5 stroke: orange
    linkStyle 6 stroke: orange
    linkStyle 7 stroke: orange
    linkStyle 8 stroke: orange
    linkStyle 9 stroke: orange
    linkStyle 10 stroke: orange
    linkStyle 11 stroke: orange
```

#### Meta Contract Spender

Token approval with a meta transaction where the spender is a contract. On the
2/A path the spender contract itself allows meta transactions, so the spender
transfers the token with a meta transaction. On the 2/B path, the spender
transfers the token with a normal transaction.

```mermaid
flowchart TB
    off_chain_sig[Off-Chain Sig Approve] -->|Step 1| relayer[Relayer]
    relayer --> eth_nodes[ETH Nodes]
    eth_nodes --> trusted_forwarder_contract[Trusted Forwarder Contract]
    trusted_forwarder_contract --> token_contract[Token Contract]
    token_contract --> custom_token_approval[Custom Token Approval]
    
    off_chain_sig[Off-Chain Sig] -->|Step 2/A| relayer[Relayer]
    relayer -->|2/A| eth_nodes[ETH Nodes]
    eth_nodes -->|2/A| trusted_forwarder_contract
    eth_nodes -->|2/B| spender_contract[Spender Contract]
    trusted_forwarder_contract -->|2/A| spender_contract
    spender_contract --> token_contract
    token_contract --> custom_token_transfer[Custom Token Transfer]
    
    on_chain_sig_transfer[On-Chain Sig Transfer] -->|Step 2/B| eth_nodes[ETH Nodes]
    
    %% CSS-based class defs don't work
    classDef green stroke:green;
    classDef orange stroke:orange;
    
    class on_chain_sig_approve green
    class custom_token_approval green
    class trusted_forwarder_contract green
    linkStyle 0 stroke: green
    linkStyle 1 stroke: green
    linkStyle 2 stroke: green
    linkStyle 3 stroke: green
    linkStyle 4 stroke: green
    
    class on_chain_sig_transfer orange
    class custom_token_transfer orange
    class spender_contract orange
    linkStyle 5 stroke: orange
    linkStyle 6 stroke: orange
    linkStyle 7 stroke: orange
    linkStyle 8 stroke: orange
    linkStyle 9 stroke: orange
    linkStyle 10 stroke: orange
    linkStyle 11 stroke: orange
    linkStyle 12 stroke: orange
```
