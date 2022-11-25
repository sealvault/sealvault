// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

table! {
    account_pictures (deterministic_id) {
        deterministic_id -> Text,
        image_name -> Nullable<Text>,
        image_hash -> Binary,
        image -> Binary,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    accounts (deterministic_id) {
        deterministic_id -> Text,
        uuid -> Text,
        name -> Text,
        picture_id -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    addresses (deterministic_id) {
        deterministic_id -> Text,
        asymmetric_key_id -> Text,
        chain_id -> Text,
        address -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    asymmetric_keys (deterministic_id) {
        deterministic_id -> Text,
        account_id -> Text,
        dek_id -> Text,
        elliptic_curve -> Text,
        public_key -> Binary,
        encrypted_der -> Binary,
        is_account_wallet -> Bool,
        dapp_id -> Nullable<Text>,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    chains (deterministic_id) {
        deterministic_id -> Text,
        protocol -> Text,
        protocol_data -> Text,
        user_settings -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    dapps (deterministic_id) {
        deterministic_id -> Text,
        identifier -> Text,
        url -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    data_encryption_keys (deterministic_id) {
        deterministic_id -> Text,
        name -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    data_migrations (deterministic_id) {
        deterministic_id -> Text,
        version -> Text,
        description -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    local_dapp_sessions (uuid) {
        uuid -> Text,
        address_id -> Text,
        dapp_id -> Text,
        last_used_at -> Text,
        updated_at -> Text,
        created_at -> Text,
    }
}

table! {
    local_encrypted_deks (id) {
        id -> Integer,
        dek_id -> Text,
        encrypted_dek -> Binary,
        kek_name -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

table! {
    local_settings (id) {
        id -> Text,
        account_id -> Text,
        pending_backup_version -> Integer,
        completed_backup_version -> Integer,
        backup_completed_at -> Nullable<Text>,
        backup_password_updated_at -> Nullable<Text>,
        backup_kdf_nonce -> Nullable<Binary>,
    }
}

joinable!(accounts -> account_pictures (picture_id));
joinable!(addresses -> asymmetric_keys (asymmetric_key_id));
joinable!(addresses -> chains (chain_id));
joinable!(asymmetric_keys -> accounts (account_id));
joinable!(asymmetric_keys -> dapps (dapp_id));
joinable!(asymmetric_keys -> data_encryption_keys (dek_id));
joinable!(local_dapp_sessions -> addresses (address_id));
joinable!(local_dapp_sessions -> dapps (dapp_id));
joinable!(local_encrypted_deks -> data_encryption_keys (dek_id));
joinable!(local_settings -> accounts (account_id));

allow_tables_to_appear_in_same_query!(
    account_pictures,
    accounts,
    addresses,
    asymmetric_keys,
    chains,
    dapps,
    data_encryption_keys,
    data_migrations,
    local_dapp_sessions,
    local_encrypted_deks,
    local_settings,
);
