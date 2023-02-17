CREATE TABLE tokens
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,

    -- Eg. contract address
    address       TEXT            NOT NULL,
    chain_id         TEXT            NOT NULL,
    type             TEXT CHECK( type IN ('fungible', 'nft') )  NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT,

    FOREIGN KEY (chain_id) REFERENCES chains (deterministic_id),

    UNIQUE (address, chain_id, type)
);

CREATE INDEX IF NOT EXISTS tokens_address_idx on tokens (address);

CREATE TABLE tokens_to_addresses
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,

    token_id          TEXT             NOT NULL,
    address_id        TEXT             NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT,

    FOREIGN KEY (token_id) REFERENCES tokens (deterministic_id),
    FOREIGN KEY (address_id) REFERENCES addresses (deterministic_id),

    UNIQUE (token_id, address_id)
);

CREATE INDEX IF NOT EXISTS tokens_to_addresses_address_id_idx on tokens_to_addresses (address_id);
