// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// Based on: https://github.com/kornelski/rust-security-framework/
use crate::encryption::key_material::KeyMaterial;
use crate::encryption::keychains::keychain::KeychainImpl;
use crate::encryption::KeyEncryptionKey;
use crate::{config, Error};
use core_foundation::base::CFType;
use core_foundation::base::TCFType;
use core_foundation::boolean::CFBoolean;
use core_foundation::data::CFData;
use core_foundation::dictionary::CFDictionary;
use core_foundation::string::CFString;
use core_foundation_sys::base::{CFGetTypeID, CFRelease};
use core_foundation_sys::base::{CFTypeRef, OSStatus};
use core_foundation_sys::data::CFDataRef;
use core_foundation_sys::dictionary::CFDictionaryRef;
use core_foundation_sys::string::CFStringRef;
use std::cell::Cell;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};

pub(super) struct IOSKeychain {
    internal: Arc<Mutex<IOSKeychainInternal>>,
}

impl IOSKeychain {
    pub fn new() -> Self {
        let internal = Arc::new(Mutex::new(IOSKeychainInternal::new()));
        Self { internal }
    }

    fn put(&self, key: KeyEncryptionKey, storage: KeychainStorage) -> Result<(), Error> {
        let keychain = self.internal.lock()?;
        keychain.put(key, storage)
    }
}

impl Debug for IOSKeychain {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IOSKeychain").finish()
    }
}

impl KeychainImpl for IOSKeychain {
    fn get(&self, name: &str) -> Result<KeyEncryptionKey, Error> {
        let keychain = self.internal.lock()?;
        let key_material = keychain.get(name)?;
        Ok(KeyEncryptionKey::new(name.into(), key_material))
    }

    fn put_local_unlocked(&self, key: KeyEncryptionKey) -> Result<(), Error> {
        self.put(key, KeychainStorage::WhenUnlockedLocal)
    }
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

    fn get(&self, name: &str) -> Result<KeyMaterial, Error> {
        let query = get_query(name);
        let params = CFDictionary::from_CFType_pairs(&query);

        let mut result: CFTypeRef = std::ptr::null();
        let status =
            unsafe { SecItemCopyMatching(params.as_concrete_TypeRef(), &mut result) };

        return if status != 0 {
            Err(Error::Fatal {
                error: format!("Keychain returned error code: {}", status),
            })
        } else if result.is_null() {
            Err(Error::Fatal {
                error: format!("Key not found in keychain: '{}'", name),
            })
        } else {
            let type_id = unsafe { CFGetTypeID(result) };
            if type_id != CFData::type_id() {
                // Unexpected: we got a reference to some other type.
                // Release it to make sure there's no leak, but
                // we can't return the password in this case.
                unsafe { CFRelease(result) };

                Err(Error::Fatal {
                    error: format!("Expected CFData type id, instead got '{}'", type_id),
                })
            } else {
                let result = result as CFDataRef;
                let data = unsafe { CFData::wrap_under_create_rule(result) };
                // `len()` returns `isize` for some reason.
                let length: usize = data.len().try_into().map_err(|_| Error::Fatal {
                    error: format!("Got negative buffer length: {}", data.len()),
                })?;

                let key = KeyMaterial::from_slice(data.bytes())?;

                // Zeroize the buffer returned by iOS keychain manually.
                let ptr = data.bytes().as_ptr();
                if ptr.is_null() {
                    Err(Error::Fatal {
                        error: "Keychain item data pointer is null.".into(),
                    })
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

    fn put(
        &self,
        key: KeyEncryptionKey,
        class: KeychainStorage,
    ) -> Result<(), Error> {
        let (name, key_material) = key.into_keychain();
        let wrapped_value = Arc::new(key_material);
        let query = class.put_query(&name, wrapped_value);
        let params = CFDictionary::from_CFType_pairs(&query);

        // We signal that we don't need the result by passing the null pointer.
        let mut result = std::ptr::null();
        let status = unsafe { SecItemAdd(params.as_concrete_TypeRef(), &mut result) };

        if status == 0 {
            Ok(())
        } else {
            Err(Error::Fatal {
                error: format!(
                    "Saving '{}' to keychain failed with error {}",
                    name, status
                ),
            })
        }
    }
}

fn get_query(name: &str) -> Vec<(CFString, CFType)> {
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
        (
            unsafe { CFString::wrap_under_get_rule(kSecReturnData) },
            CFBoolean::from(true).as_CFType(),
        ),
    ]
}

enum KeychainStorage {
    WhenUnlockedLocal,
}

impl KeychainStorage {
    fn put_query(&self, name: &str, value: Arc<KeyMaterial>) -> Vec<(CFString, CFType)> {
        // SAFETY:
        // See `get_query`.
        let query = vec![
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
            (
                unsafe { CFString::wrap_under_get_rule(kSecValueData) },
                // Best effort to create a `CFData` referencing buffer without creating a copy.
                // We want to avoid a copy to make sure we can zeroize the buffer.
                // Unfortunately, the underlying Core Foundation `CFDataCreateWithBytesNoCopy`
                // doesn't actually make a hard guarantee that there will be no copy.
                CFData::from_arc(value).as_CFType(),
            ),
        ];
        query
    }

    unsafe fn sec_attr_accessible(&self) -> CFStringRef {
        match self {
            Self::WhenUnlockedLocal => kSecAttrAccessibleWhenPasscodeSetThisDeviceOnly,
        }
    }

    fn sec_attr_synchronizable(&self) -> bool {
        match self {
            Self::WhenUnlockedLocal => false,
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

    static kSecAttrSynchronizable: CFStringRef;

    static kSecValueData: CFStringRef;

    static kSecReturnData: CFStringRef;

    /// Adds one or more items to a keychain.
    pub fn SecItemAdd(attributes: CFDictionaryRef, result: *mut CFTypeRef) -> OSStatus;

    /// Returns one or more keychain items that match a search query, or copies attributes of specific keychain items.
    pub fn SecItemCopyMatching(
        query: CFDictionaryRef,
        result: *mut CFTypeRef,
    ) -> OSStatus;
}
