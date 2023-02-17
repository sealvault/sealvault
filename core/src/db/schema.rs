// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

diesel::table! {
    addresses (deterministic_id) {
        deterministic_id -> Text,
        asymmetric_key_id -> Text,
        chain_id -> Text,
        address -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    asymmetric_keys (deterministic_id) {
        deterministic_id -> Text,
        profile_id -> Text,
        dek_id -> Text,
        elliptic_curve -> Text,
        public_key -> Binary,
        encrypted_der -> Binary,
        is_profile_wallet -> Bool,
        dapp_id -> Nullable<Text>,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    chains (deterministic_id) {
        deterministic_id -> Text,
        protocol -> Text,
        protocol_data -> Text,
        user_settings -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    dapps (deterministic_id) {
        deterministic_id -> Text,
        identifier -> Text,
        url -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    data_encryption_keys (deterministic_id) {
        deterministic_id -> Text,
        name -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    data_migrations (deterministic_id) {
        deterministic_id -> Text,
        version -> Text,
        description -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    local_dapp_sessions (uuid) {
        uuid -> Text,
        address_id -> Text,
        dapp_id -> Text,
        last_used_at -> Text,
        updated_at -> Text,
        created_at -> Text,
    }
}

diesel::table! {
    local_encrypted_deks (id) {
        id -> Integer,
        dek_id -> Text,
        encrypted_dek -> Binary,
        kek_name -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    local_settings (id) {
        id -> Text,
        profile_id -> Text,
        backup_enabled -> Bool,
        // !!! `BigInt` here is a manual override. Make sure to add it back if you regenerate the
        // schema. Context: https://github.com/diesel-rs/diesel/issues/1116
        backup_version -> BigInt,
        backup_completed_at -> Nullable<Text>,
        backup_password_updated_at -> Nullable<Text>,
        backup_kdf_nonce -> Nullable<Binary>,
    }
}

diesel::table! {
    profile_pictures (deterministic_id) {
        deterministic_id -> Text,
        image_name -> Nullable<Text>,
        image_hash -> Binary,
        image -> Binary,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    profiles (deterministic_id) {
        deterministic_id -> Text,
        uuid -> Text,
        name -> Text,
        picture_id -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    tokens (deterministic_id) {
        deterministic_id -> Text,
        address -> Text,
        chain_id -> Text,
        #[sql_name = "type"]
        type_ -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::table! {
    tokens_to_addresses (deterministic_id) {
        deterministic_id -> Text,
        token_id -> Text,
        address_id -> Text,
        created_at -> Text,
        updated_at -> Nullable<Text>,
    }
}

diesel::joinable!(addresses -> asymmetric_keys (asymmetric_key_id));
diesel::joinable!(addresses -> chains (chain_id));
diesel::joinable!(asymmetric_keys -> dapps (dapp_id));
diesel::joinable!(asymmetric_keys -> data_encryption_keys (dek_id));
diesel::joinable!(asymmetric_keys -> profiles (profile_id));
diesel::joinable!(local_dapp_sessions -> addresses (address_id));
diesel::joinable!(local_dapp_sessions -> dapps (dapp_id));
diesel::joinable!(local_encrypted_deks -> data_encryption_keys (dek_id));
diesel::joinable!(local_settings -> profiles (profile_id));
diesel::joinable!(profiles -> profile_pictures (picture_id));
diesel::joinable!(tokens -> chains (chain_id));
diesel::joinable!(tokens_to_addresses -> addresses (address_id));
diesel::joinable!(tokens_to_addresses -> tokens (token_id));

diesel::allow_tables_to_appear_in_same_query!(
    addresses,
    asymmetric_keys,
    chains,
    dapps,
    data_encryption_keys,
    data_migrations,
    local_dapp_sessions,
    local_encrypted_deks,
    local_settings,
    profile_pictures,
    profiles,
    tokens,
    tokens_to_addresses,
);
