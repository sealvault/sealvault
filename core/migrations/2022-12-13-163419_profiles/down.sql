ALTER TABLE `profiles` RENAME TO `accounts`;

ALTER TABLE `profile_pictures` RENAME TO `account_pictures`;

ALTER TABLE `asymmetric_keys` RENAME COLUMN `profile_id` TO `account_id`;
ALTER TABLE `asymmetric_keys` RENAME COLUMN `is_profile_wallet` TO `is_account_wallet`;

ALTER TABLE `local_settings` RENAME COLUMN `profile_id` TO `account_id`;
