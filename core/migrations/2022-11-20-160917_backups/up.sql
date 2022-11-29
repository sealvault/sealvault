-- Can't add `CHECK (backup_enabled IN (0, 1))` after creating table
ALTER TABLE local_settings ADD COLUMN backup_enabled BOOLEAN NOT NULL default false;
-- This has to be manually set to `BigInt` in the inferred schema by Diesel
-- See this issue why: https://github.com/diesel-rs/diesel/issues/1116
ALTER TABLE local_settings ADD COLUMN completed_backup_version INTEGER NOT NULL default 0;
ALTER TABLE local_settings ADD COLUMN backup_completed_at TEXT;
ALTER TABLE local_settings ADD COLUMN backup_password_updated_at TEXT;
ALTER TABLE local_settings ADD COLUMN backup_kdf_nonce BLOB;