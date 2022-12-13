ALTER TABLE `accounts` RENAME TO `profiles`;

ALTER TABLE `account_pictures` RENAME TO `profile_pictures`;

ALTER TABLE `asymmetric_keys` RENAME COLUMN `account_id` TO `profile_id`;
ALTER TABLE `asymmetric_keys` RENAME COLUMN `is_account_wallet` TO `is_profile_wallet`;

ALTER TABLE `local_settings` RENAME COLUMN `account_id` TO `profile_id`;