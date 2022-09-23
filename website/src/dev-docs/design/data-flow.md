# Data-Flow Diagrams

Contains assets, stores, security controls and trust boundaries.

Mitigations of attacks are in the [attack tree.](./attack-tree.md)

## Supply Chain

```mermaid
flowchart TB

  subgraph development[Development]
    direction TB

    dev[Developer]
    -->|Commit Signing| git[|borders:tb| Git]
    --> release(Release)
  end

  subgraph package_manager[Package Managers]
    direction TB

    dependencies[Dependencies]
    --> pm[|borders:tb| Package Manager]
  end

  subgraph apple[Apple]
    direction TB

    app_store[|borders:tb| App Store]
    -->|App Store Controls| install(Install)
    --> device[App]
  end

  package_manager
  --> release
  -->|Code Signing| apple
```

## Transactions


```mermaid

flowchart TB

  subgraph device[Device]
    direction TB

    keychain[|borders:bt| Local Keychain]
    db[|borders:bt| Local DB]
    secure_random(Secure Random Generator)
    browser_engine(Browser Engine)

    subgraph app[App]
      direction TB

      tx_ui(Transaction UI)
      tx_logic(Transaction Logic)
      inpage(In-page Provider)
    end


  end

  subgraph dapp[Dapp]
    direction TB

    dapp_frontend(Dapp Frontend)
    dapp_backend(Dapp Backend)

  end

  subgraph blockchain_api[Blockchain API]
    direction TB

    ba(Blockchain API)
    blockchain[|borders:bt| Blockchain]
  end


  user_action[User Action]

  dapp_frontend
  <-->|TLS| dapp_backend

  keychain[|borders:bt| Local Keychain]
  <-->|iOS Controls| tx_logic

  db[|borders:bt| Local DB]
  <-->|iOS Controls| tx_logic

  secure_random
  <--> tx_logic

  tx_logic
  <-->|Out-of-Process Rendering| inpage

  tx_logic
  <--> tx_ui

  tx_ui
  <-->|Device Lock| user_action

  tx_logic
  -->|TLS| blockchain_api

  inpage
  <--> browser_engine

  browser_engine
  <--> dapp_frontend

  dapp_frontend
  <-->|Device Lock| user_action

  dapp_frontend
  <-->|TLS| blockchain_api

  ba
  <--> blockchain[|borders:bt| Blockchain]

```

## Backup

```mermaid

flowchart TB

  subgraph device[Device]
    direction TB

    subgraph app[App]
      backup_logic(Backup Logic)
    end

    keychain[|borders:bt| Local Keychain]
    <-->|iOS Controls| backup_logic

    db[|borders:bt| Local DB]
    <-->|iOS Controls| backup_logic

  end

  subgraph icloud[iCloud]
    icloud_storage[|borders:bt| iCloud Storage]
  end

  backup_logic
  -->|Apple ID, TLS| icloud

```


