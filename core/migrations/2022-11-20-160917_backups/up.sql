ALTER TABLE local_settings ADD COLUMN pending_backup_version INTEGER NOT NULL default 0;
ALTER TABLE local_settings ADD COLUMN completed_backup_version INTEGER NOT NULL default 0;
ALTER TABLE local_settings ADD COLUMN backup_completed_at TEXT;
ALTER TABLE local_settings ADD COLUMN backup_password_updated_at TEXT;
ALTER TABLE local_settings ADD COLUMN backup_kdf_nonce BLOB;
