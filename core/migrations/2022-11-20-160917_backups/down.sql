ALTER TABLE local_settings DROP COLUMN pending_backup_version;
ALTER TABLE local_settings DROP COLUMN completed_backup_version;
ALTER TABLE local_settings DROP COLUMN backup_completed_at;
ALTER TABLE local_settings DROP COLUMN backup_password_updated_at;
ALTER TABLE local_settings DROP COLUMN backup_kdf_nonce;
