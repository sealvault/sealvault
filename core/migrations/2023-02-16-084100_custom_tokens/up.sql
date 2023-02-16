CREATE TABLE custom_tokens
(
    deterministic_id TEXT PRIMARY KEY NOT NULL,

    address          TEXT             NOT NULL,
    chain_id         TEXT             NOT NULL,
    type             TEXT CHECK( type IN ('fungible', 'nft') )  NOT NULL,

    -- RFC 3339 timestamps
    created_at       TEXT             NOT NULL,
    updated_at       TEXT,

    FOREIGN KEY (chain_id) REFERENCES chains (deterministic_id),

    UNIQUE (address, chain_id, type)
);

CREATE INDEX IF NOT EXISTS custom_tokens_address_idx on custom_tokens (address);
