PRAGMA encoding = 'UTF-8';
PRAGMA auto_vacuum = FULL;

CREATE TABLE accounts
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,

    uuid             TEXT UNIQUE      NOT NULL,
    name             TEXT             NOT NULL,
    picture_id       TEXT             NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT,

    FOREIGN KEY (picture_id) REFERENCES account_pictures (deterministic_id)
);

CREATE TABLE account_pictures
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,

    image_name       TEXT,
    image_hash       BLOB UNIQUE      NOT NULL,
    image            BLOB             NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT

);

CREATE TABLE addresses
(
    deterministic_id  TEXT PRIMARY KEY NOT NULL,
    asymmetric_key_id TEXT             NOT NULL,
    chain_id          TEXT             NOT NULL,

    address           TEXT             NOT NULL,

    -- RFC 3339 timestamps
    created_at        TEXT             NOT NULL,
    updated_at        TEXT,

    FOREIGN KEY (asymmetric_key_id) REFERENCES asymmetric_keys (deterministic_id),
    FOREIGN KEY (chain_id) REFERENCES chains (deterministic_id),

    UNIQUE (asymmetric_key_id, chain_id)
);

CREATE INDEX IF NOT EXISTS addresses_address_idx on addresses (address);

CREATE TABLE asymmetric_keys
(
    deterministic_id  TEXT PRIMARY KEY NOT NULL,
    account_id        TEXT             NOT NULL,
    dek_id            TEXT             NOT NULL,

    elliptic_curve    TEXT             NOT NULL,
    --- ASN.1 DER format
    public_key        BLOB UNIQUE      NOT NULL,

    -- 24 byte random nonce + encrypted SEC1 ASN.1 DER ECPrivateKey format
    -- See `EncryptionOutput` serialization for details.
    encrypted_der     BLOB             NOT NULL,

    -- Applications
    is_account_wallet BOOLEAN          NOT NULL,
    dapp_id           TEXT,

    -- RFC 3339 timestamps
    created_at        TEXT             NOT NULL,
    updated_at        TEXT,

    FOREIGN KEY (account_id) REFERENCES accounts (deterministic_id),
    FOREIGN KEY (dek_id) REFERENCES data_encryption_keys (deterministic_id),
    FOREIGN KEY (dapp_id) REFERENCES dapps (deterministic_id),

    -- Sqlite emulates booleans with integers.
    CHECK (is_account_wallet IN (0, 1)),
    -- A key cannot be associated with a dapp and used as an account wallet at the same time.
    CHECK (dapp_id IS NULL OR is_account_wallet IS FALSE)
);

CREATE TABLE chains
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,

    protocol         TEXT             NOT NULL,
    -- Protocol-specific JSON data, eg. chain id for Ethereum.
    protocol_data    TEXT             NOT NULL,
    -- Chain specific user settings for the chain as JSON, eg. default amount of native
    -- token to transfer to new dapp addresses.
    user_settings    TEXT             NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT,

    UNIQUE (protocol, protocol_data)
);

CREATE TABLE dapps
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,

    -- Registrable domain or origin if there is no registrable domain (eg. localhost or file url)
    identifier       TEXT UNIQUE      NOT NULL,
    -- The url from which the dapp was added.
    url              TEXT NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT
);

CREATE TABLE data_migrations
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,
    version          TEXT UNIQUE      NOT NULL,
    description      TEXT             NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT
);

CREATE TABLE data_encryption_keys
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,

    name             TEXT UNIQUE      NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT
);

-- Keeps track of which address is used on which chain for a dapp.
CREATE TABLE local_dapp_sessions
(
    -- uuid to prevent accidental reuse with integer ids
    uuid           TEXT PRIMARY KEY NOT NULL,

    address_id   TEXT UNIQUE NOT NULL,
    dapp_id      TEXT        NOT NULL,

    -- RFC 3339 timestamps
    last_used_at TEXT        NOT NULL,
    updated_at   TEXT        NOT NULL,
    created_at   TEXT        NOT NULL,

    FOREIGN KEY (address_id) REFERENCES addresses (deterministic_id),
    FOREIGN KEY (dapp_id) REFERENCES dapps (deterministic_id)
);

-- Data encryption key store
-- One DEK may be stored multiple times encrypted with different KEKs.
CREATE TABLE local_encrypted_deks
(
    id            INTEGER PRIMARY KEY NOT NULL,
    dek_id        TEXT NOT NULL,

    -- 24 byte random nonce + encrypted DEK
    -- See `EncryptionOutput` serialization for details.
    encrypted_dek BLOB NOT NULL,

    -- Key encryption keys are stored outside the DB (eg. iOS Keychain or user self-custody)
    kek_name      TEXT NOT NULL,

    -- RFC 3339 timestamps
    created_at    TEXT NOT NULL,
    updated_at    TEXT,

    FOREIGN KEY (dek_id) REFERENCES data_encryption_keys (deterministic_id),

    UNIQUE (dek_id, kek_name)
);

-- User's local app settings. Singleton.
CREATE TABLE local_settings
(
    -- Id is text, because it's a singleton.
    id         TEXT PRIMARY KEY NOT NULL,
    -- Currently selected account id
    account_id TEXT             NOT NULL,

    FOREIGN KEY (account_id) REFERENCES accounts (deterministic_id),
    -- Singleton table
    CHECK (id = 'local_settings')
);

