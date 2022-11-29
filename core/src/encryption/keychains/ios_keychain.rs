// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// Based on: https://github.com/kornelski/rust-security-framework/
use std::{
    cell::Cell,
    fmt::{Debug, Formatter},
    marker::PhantomData,
    sync::{Arc, Mutex},
};

use core_foundation::{
    base::{CFType, TCFType},
    boolean::CFBoolean,
    data::CFData,
    dictionary::CFDictionary,
    string::CFString,
};
use core_foundation_sys::{
    base::{CFGetTypeID, CFRelease, CFTypeRef, OSStatus},
    data::CFDataRef,
    dictionary::CFDictionaryRef,
    string::CFStringRef,
};
use generic_array::ArrayLength;

use crate::{
    config,
    device::DeviceIdentifier,
    encryption::{
        key_material::KeyMaterial,
        keychains::keychain::{KeychainError, KeychainImpl},
        KeyName,
    },
    Error,
};

pub(super) struct IOSKeychain {
    // It's a Mutex, instead of a RwLock because we only want access from one thread for reads as
    // well in order to zeroize the buffer returned from the keychain safely.
    internal: Arc<Mutex<IOSKeychainInternal>>,
}

impl IOSKeychain {
    pub fn new() -> Self {
        let internal = Arc::new(Mutex::new(IOSKeychainInternal::new()));
        Self { internal }
    }
}

impl Debug for IOSKeychain {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IOSKeychain").finish()
    }
}

impl KeychainImpl for IOSKeychain {
    fn get_local<N: ArrayLength<u8>>(
        &self,
        key_name: KeyName,
    ) -> Result<KeyMaterial<N>, KeychainError> {
        let keychain = self.internal.lock()?;
        keychain.get::<N>(key_name.into(), KeychainStorage::WhenUnlockedLocal)
    }

    fn get_synced<N: ArrayLength<u8>>(
        &self,
        device_identifier: &DeviceIdentifier,
        key_name: KeyName,
    ) -> Result<KeyMaterial<N>, KeychainError> {
        let keychain = self.internal.lock()?;
        let name = synced_name(device_identifier, key_name);
        keychain.get::<N>(&name, KeychainStorage::WhenUnlockedSynced)
    }

    fn upsert_local<N: ArrayLength<u8>>(
        &self,
        key_name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), KeychainError> {
        let keychain = self.internal.lock()?;
        keychain.upsert(key_name.into(), key, KeychainStorage::WhenUnlockedLocal)
    }

    fn upsert_synced<N: ArrayLength<u8>>(
        &self,
        device_identifier: &DeviceIdentifier,
        key_name: KeyName,
        key: KeyMaterial<N>,
    ) -> Result<(), KeychainError> {
        let keychain = self.internal.lock()?;
        let name = synced_name(device_identifier, key_name);
        keychain.upsert(&name, key, KeychainStorage::WhenUnlockedSynced)
    }

    fn delete_local(&self, key_name: KeyName) -> Result<(), KeychainError> {
        let keychain = self.internal.lock()?;
        keychain.delete(key_name.into(), KeychainStorage::WhenUnlockedLocal)?;
        Ok(())
    }

    fn delete_synced(
        &self,
        device_identifier: &DeviceIdentifier,
        key_name: KeyName,
    ) -> Result<(), KeychainError> {
        let keychain = self.internal.lock()?;
        let name = synced_name(device_identifier, key_name);
        keychain.delete(&name, KeychainStorage::WhenUnlockedSynced)?;
        Ok(())
    }
}

// We use sync for backup, not for simultaneous access from multiple devices. We use device specific
// names to allow rotating secrets on a device without affecting other devices.
fn synced_name(device_identifier: &DeviceIdentifier, name: KeyName) -> String {
    format!("{}_{}", name.as_ref(), device_identifier.as_ref())
}

/// Helper that we mark as not sync due to unsafe calls.
struct IOSKeychainInternal {
    // Hack to make `IOSKeychainInternal` not sync. A more elegant solution would be marking it is
    // `!Sync`, but that feature is unstable: https://github.com/rust-lang/rust/issues/68318
    _guard: PhantomData<Cell<()>>,
}

impl IOSKeychainInternal {
    fn new() -> Self {
        Self {
            _guard: Default::default(),
        }
    }

    fn get<N: ArrayLength<u8>>(
        &self,
        name: &str,
        storage_class: KeychainStorage,
    ) -> Result<KeyMaterial<N>, KeychainError> {
        let query = storage_class.get_query(name);
        let params = CFDictionary::from_CFType_pairs(&query);

        let mut result: CFTypeRef = std::ptr::null();
        let status =
            unsafe { SecItemCopyMatching(params.as_concrete_TypeRef(), &mut result) };

        return if status != 0 {
            Err(KeychainError::FailedToGet {
                name: name.into(),
                code: status,
            })
        } else if result.is_null() {
            Err(KeychainError::NotFound { name: name.into() })
        } else {
            let type_id = unsafe { CFGetTypeID(result) };
            if type_id != CFData::type_id() {
                // Unexpected: we got a reference to some other type.
                // Release it to make sure there's no leak, but
                // we can't return the password in this case.
                unsafe { CFRelease(result) };

                Err(Error::Fatal {
                    error: format!("Expected CFData type id, instead got '{}'", type_id),
                }
                .into())
            } else {
                let result = result as CFDataRef;
                let data = unsafe { CFData::wrap_under_create_rule(result) };
                // `len()` returns `isize` for some reason.
                let length: usize = data.len().try_into().map_err(|_| Error::Fatal {
                    error: format!("Got negative buffer length: {}", data.len()),
                })?;

                let key = KeyMaterial::<N>::from_slice(data.bytes())?;

                // Zeroize the buffer returned by iOS keychain manually.
                let ptr = data.bytes().as_ptr();
                if ptr.is_null() {
                    Err(Error::Fatal {
                        error: "Keychain item data pointer is null.".into(),
                    }
                    .into())
                } else {
                    unsafe {
                        // SAFETY:
                        // 1. We own the `CFData` behind `data` which gets released when it goes out
                        // of scope on drop (ie. cannot be released at this point).
                        // 2. Bytes are always aligned.
                        // 3. We check that it's not the null pointer.
                        // 4. Only one instance of this code can run at a time, because the struct is wrapped in a
                        // mutex.
                        // So it's safe to cast to mutable even though the library doesn't let us
                        // get a mutable pointer.
                        std::ptr::write_bytes(ptr as *mut u8, 0x0, length);
                    }
                    Ok(key)
                }
            }
        };
    }

    fn upsert<N: ArrayLength<u8>>(
        &self,
        name: &str,
        key: KeyMaterial<N>,
        storage_class: KeychainStorage,
    ) -> Result<(), KeychainError> {
        let value = Arc::new(key);
        self.put(name, value.clone(), storage_class)
            .or_else(|err| match err {
                KeychainError::DuplicateItem { .. } => {
                    self.update(name, value, storage_class)
                }
                error => Err(error),
            })
    }

    fn put<N: ArrayLength<u8>>(
        &self,
        name: &str,
        key: Arc<KeyMaterial<N>>,
        storage_class: KeychainStorage,
    ) -> Result<(), KeychainError> {
        let query = storage_class.put_query::<N>(name, key);
        let params = CFDictionary::from_CFType_pairs(&query);

        // We signal that we don't need the result by passing the null pointer.
        let mut result = std::ptr::null();
        let status = unsafe { SecItemAdd(params.as_concrete_TypeRef(), &mut result) };

        if status == 0 {
            Ok(())
        } else if status == ERR_SEC_DUPLICATE_ITEM {
            Err(KeychainError::DuplicateItem { name: name.into() })
        } else {
            Err(KeychainError::FailedToPut {
                name: name.into(),
                code: status,
            })
        }
    }

    fn update<N: ArrayLength<u8>>(
        &self,
        name: &str,
        key: Arc<KeyMaterial<N>>,
        storage_class: KeychainStorage,
    ) -> Result<(), KeychainError> {
        let query = storage_class.base_query(name);
        let query_params = CFDictionary::from_CFType_pairs(&query);

        let set_value = KeychainStorage::set_value(key);
        let set_value_params = CFDictionary::from_CFType_pairs(&set_value);

        let status = unsafe {
            SecItemUpdate(
                query_params.as_concrete_TypeRef(),
                set_value_params.as_concrete_TypeRef(),
            )
        };

        if status == 0 {
            Ok(())
        } else if status == ERR_SEC_ITEM_NOT_FOUND {
            Err(KeychainError::NotFound { name: name.into() })
        } else {
            Err(KeychainError::FailedToUpdate {
                name: name.into(),
                code: status,
            })
        }
    }

    /// Delete the keychain entry for the name.
    fn delete(
        &self,
        name: &str,
        storage_class: KeychainStorage,
    ) -> Result<(), KeychainError> {
        let query = storage_class.base_query(name);
        let params = CFDictionary::from_CFType_pairs(&query);

        let status = unsafe { SecItemDelete(params.as_concrete_TypeRef()) };

        // Ok if not found to make it idempotent.
        if status == 0 {
            Ok(())
        } else if status == ERR_SEC_ITEM_NOT_FOUND {
            Err(KeychainError::NotFound { name: name.into() })
        } else {
            Err(KeychainError::FailedToDelete {
                name: name.into(),
                code: status,
            })
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum KeychainStorage {
    WhenUnlockedLocal,
    WhenUnlockedSynced,
}

impl KeychainStorage {
    fn base_query(&self, name: &str) -> Vec<(CFString, CFType)> {
        // SAFETY:
        // The query strings are static `CFStringRef`, but we need to pass `CFString`. The
        // solution is to get a non-owning `CFString` reference with the Core Foundation's
        // get rule. This is not safe by default, since a dynamic object could be released
        // while we hold a non-owning reference to them, but it's safe in this case, because
        // the wrapped objects are static.
        vec![
            (
                unsafe { CFString::wrap_under_get_rule(kSecClass) },
                unsafe {
                    CFString::wrap_under_get_rule(kSecClassGenericPassword).as_CFType()
                },
            ),
            (
                unsafe { CFString::wrap_under_get_rule(kSecAttrService) },
                CFString::from(config::IOS_SERVICE).as_CFType(),
            ),
            (
                unsafe { CFString::wrap_under_get_rule(kSecAttrAccount) },
                CFString::from(name).as_CFType(),
            ),
            // The service and the name identify the item, we include the accessible and
            // synchronize attributes as a defensive measure for soft delete.
            (
                unsafe { CFString::wrap_under_get_rule(kSecAttrAccessible) },
                unsafe {
                    CFString::wrap_under_get_rule(self.sec_attr_accessible()).as_CFType()
                },
            ),
            (
                unsafe { CFString::wrap_under_get_rule(kSecAttrSynchronizable) },
                CFBoolean::from(self.sec_attr_synchronizable()).as_CFType(),
            ),
        ]
    }

    fn get_query(&self, name: &str) -> Vec<(CFString, CFType)> {
        let mut query = self.base_query(name);
        query.push((
            unsafe { CFString::wrap_under_get_rule(kSecReturnData) },
            CFBoolean::from(true).as_CFType(),
        ));
        query
    }

    fn put_query<N: ArrayLength<u8>>(
        &self,
        name: &str,
        value: Arc<KeyMaterial<N>>,
    ) -> Vec<(CFString, CFType)> {
        let mut query = self.base_query(name);
        let value = Self::set_value(value);
        query.extend(value.into_iter());
        query
    }

    fn set_value<N: ArrayLength<u8>>(
        value: Arc<KeyMaterial<N>>,
    ) -> Vec<(CFString, CFType)> {
        vec![(
            unsafe { CFString::wrap_under_get_rule(kSecValueData) },
            // Best effort to create a `CFData` referencing buffer without creating a copy.
            // We want to avoid a copy to make sure we can zeroize the buffer.
            // Unfortunately, the underlying Core Foundation `CFDataCreateWithBytesNoCopy`
            // doesn't actually make a hard guarantee that there will be no copy.
            CFData::from_arc(value).as_CFType(),
        )]
    }

    unsafe fn sec_attr_accessible(&self) -> CFStringRef {
        match self {
            Self::WhenUnlockedLocal => kSecAttrAccessibleWhenPasscodeSetThisDeviceOnly,
            // Synced implies that a passcode is set.
            Self::WhenUnlockedSynced => kSecAttrAccessibleWhenUnlocked,
        }
    }

    fn sec_attr_synchronizable(&self) -> bool {
        match self {
            Self::WhenUnlockedLocal => false,
            Self::WhenUnlockedSynced => true,
        }
    }
}

extern "C" {
    /// Static strings defined in Core Foundation
    static kSecClass: CFStringRef;
    static kSecClassGenericPassword: CFStringRef;

    static kSecAttrService: CFStringRef;
    static kSecAttrAccount: CFStringRef;

    static kSecAttrAccessible: CFStringRef;

    static kSecAttrAccessibleWhenPasscodeSetThisDeviceOnly: CFStringRef;
    static kSecAttrAccessibleWhenUnlocked: CFStringRef;

    static kSecAttrSynchronizable: CFStringRef;

    static kSecValueData: CFStringRef;

    static kSecReturnData: CFStringRef;

    /// Adds one or more items to a keychain.
    pub fn SecItemAdd(attributes: CFDictionaryRef, result: *mut CFTypeRef) -> OSStatus;

    /// Modifies items that match a search query.
    #[allow(non_snake_case)]
    pub fn SecItemUpdate(
        query: CFDictionaryRef,
        attributesToUpdate: CFDictionaryRef,
    ) -> OSStatus;

    /// Returns one or more keychain items that match a search query, or copies attributes of specific keychain items.
    pub fn SecItemCopyMatching(
        query: CFDictionaryRef,
        result: *mut CFTypeRef,
    ) -> OSStatus;

    /// Deletes items that match a search query.
    pub fn SecItemDelete(query: CFDictionaryRef) -> OSStatus;
}

const ERR_SEC_ITEM_NOT_FOUND: OSStatus = -25300;
const ERR_SEC_DUPLICATE_ITEM: OSStatus = -25299;
