// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashSet, str::FromStr};

use generic_array::{typenum::U20, GenericArray};
use lazy_static::lazy_static;
use rand::Rng;

use crate::{
    encryption::{key_material::KeyMaterial, KeyName, Keychain},
    Error,
};

const PASSWORD_LENGTH: usize = 20;
type PasswordArray = GenericArray<u8, U20>;

lazy_static! {
    // Crockford's base 32 alphabet: https://www.crockford.com/base32.html
    static ref ALPHABET: Vec<u8> = {
        let chars: &[u8] = b"0123456789ABCDEFGHJKMNPQRSTVWXYZ";
        chars.to_vec()
    };

    static ref CHAR_SET: HashSet<char> = HashSet::from_iter(
        ALPHABET.iter().cloned().map(|c| c as char)
    );
}

/// The self-custody cloud backup password for the user with 100-bit entropy.
/// More: https://sealvault.org/dev-docs/design/backup/#backup-password
pub struct BackupPassword(KeyMaterial<U20>);

impl BackupPassword {
    fn new(password: Box<PasswordArray>) -> Result<Self, Error> {
        let key_material = KeyMaterial::new(password)?;
        Ok(Self(key_material))
    }

    pub(super) fn random() -> Result<Self, Error> {
        let mut rng = rand::thread_rng();

        // Allocate on heap here to prevent unreachable copies for zeroization
        let mut password: Box<PasswordArray> = Box::default();
        for i in 0..PASSWORD_LENGTH {
            // No fallible interface for gen_range unfortunately. It should panic if insufficient
            // entropy, but not guaranteed.
            let abc_index = rng.gen_range(0..ALPHABET.len());
            (*password)[i] = ALPHABET[abc_index];
        }

        BackupPassword::new(password)
    }

    pub fn setup(keychain: &Keychain) -> Result<Self, Error> {
        let backup_password = Self::random()?;
        backup_password.save_to_local_keychain(keychain)?;
        Self::from_keychain(keychain)
    }

    pub fn from_keychain(keychain: &Keychain) -> Result<Self, Error> {
        let key = keychain.get(KeyName::BackupPassword)?;
        Ok(Self(key))
    }

    pub(super) fn expose_secret(&self) -> &[u8] {
        self.0.as_ref()
    }

    /// Display the backup password to the user in groups of 5 separated by dashes, eg.
    /// "8FD93-EYWZR-GB7HX-QAVNS".
    /// No fmt::Display implementation, since this method should be only used for display in the UI.
    /// String is not zeroized because it's passed through FFI where we can't guarantee zeroization.
    #[allow(dead_code)]
    pub fn display_to_user(&self) -> String {
        const GROUP_SIZE: usize = 5;
        let dashes = PASSWORD_LENGTH / GROUP_SIZE;
        let mut res = String::with_capacity(PASSWORD_LENGTH + dashes);
        for i in 0..dashes {
            let start = i * GROUP_SIZE;
            let end = start + GROUP_SIZE;
            // let slice = &self.0.as_ref()[start..end];
            let slice: &[u8] = self.0.as_ref();
            for c in &slice[start..end] {
                res.push(*c as char)
            }
            if i < dashes - 1 {
                res.push('-')
            }
        }
        res
    }

    /// Save the backup password to the local keychain.
    pub fn save_to_local_keychain(self, keychain: &Keychain) -> Result<(), Error> {
        keychain.put_local(KeyName::BackupPassword, self.0)
    }

    /// Delete the backup password from the local keychain.
    /// This should be only called to roll back the initial data migration, hence the deprecation
    /// warning.
    #[deprecated]
    pub fn delete_from_keychain(keychain: &Keychain) -> Result<(), Error> {
        keychain.delete(KeyName::BackupPassword)
    }
}

/// Decode character according to Crockford's base 32 alphabet: https://www.crockford.com/base32.html
fn decode_symbol(symbol: char) -> Option<char> {
    let upper_symbol = symbol.to_uppercase().next()?;
    match upper_symbol {
        // Uppercase variants only here for completeness
        '0' | 'O' | 'o' => Some('0'),
        '1' | 'I' | 'i' | 'L' | 'l' => Some('1'),
        s if CHAR_SET.contains(&s) => Some(s),
        _ => None,
    }
}

impl FromStr for BackupPassword {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Allocate on heap here to prevent unreachable copies for zeroization
        let mut password: Box<PasswordArray> = Default::default();
        let mut i: usize = 0;
        for c in s.chars() {
            if let Some(symbol) = decode_symbol(c) {
                if i >= PASSWORD_LENGTH {
                    return Err(Error::User {
                        explanation: "Password too long".to_string(),
                    });
                }
                // Symbols in the character set are guaranteed to fit into u8.
                password[i] = symbol as u8;
                i += 1;
            }
        }
        if i < PASSWORD_LENGTH {
            return Err(Error::User {
                explanation: "Password too short".to_string(),
            });
        }
        BackupPassword::new(password)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use regex::Regex;

    use super::*;

    #[test]
    fn charset_size() {
        let expected_length = 32;
        assert_eq!(ALPHABET.len(), expected_length);
        assert_eq!(CHAR_SET.len(), expected_length);
    }

    #[test]
    fn decode_symbol_identity() {
        for c in ALPHABET.clone() {
            let c = c as char;
            assert_eq!(decode_symbol(c), Some(c))
        }
    }

    #[test]
    fn decode_symbol_lowercase() {
        for c in ALPHABET.clone() {
            let c = c as char;
            let lc = c.to_lowercase().next().unwrap();
            assert_eq!(decode_symbol(lc), Some(c))
        }
    }

    #[test]
    fn decode_symbol_custom() {
        assert_eq!(decode_symbol('0'), Some('0'));
        assert_eq!(decode_symbol('O'), Some('0'));
        assert_eq!(decode_symbol('o'), Some('0'));

        assert_eq!(decode_symbol('1'), Some('1'));
        assert_eq!(decode_symbol('I'), Some('1'));
        assert_eq!(decode_symbol('i'), Some('1'));
        assert_eq!(decode_symbol('L'), Some('1'));
        assert_eq!(decode_symbol('l'), Some('1'));
    }

    #[test]
    fn decode_symbol_missing() {
        assert_eq!(decode_symbol('U'), None);
        assert_eq!(decode_symbol('u'), None);
        assert_eq!(decode_symbol('-'), None);
        assert_eq!(decode_symbol('_'), None);
    }

    #[test]
    fn display_format() {
        let password = BackupPassword::random().expect("random ok");
        let display = password.display_to_user();

        let re = Regex::new(r"^\w{5}-\w{5}-\w{5}-\w{5}$").expect("regex is ok");
        assert!(re.is_match(&display));
    }

    #[test]
    fn display_parse() -> Result<()> {
        let password = BackupPassword::random()?;
        let display = password.display_to_user();

        let _parsed: BackupPassword = display.parse()?;
        Ok(())
    }

    #[test]
    fn parse_without_separator() -> Result<()> {
        let _parsed: BackupPassword = "8FD93EYWZRGB7HXQAVNS".parse()?;
        Ok(())
    }

    #[test]
    fn parse_with_one_separator() -> Result<()> {
        let _parsed: BackupPassword = "8FD93-EYWZRGB7HXQAVNS".parse()?;
        Ok(())
    }

    #[test]
    fn parse_with_lowercase() -> Result<()> {
        let _parsed: BackupPassword = "8FD93-EYWzR-GB7HX-qavns".parse()?;
        Ok(())
    }

    #[test]
    fn parse_empty() {
        let result: Result<BackupPassword, Error> = "".parse();
        assert!(matches!(result, Err(Error::User { explanation: _ })))
    }

    #[test]
    fn parse_no_valid_char() {
        let result: Result<BackupPassword, Error> = "@_!".parse();
        assert!(matches!(result, Err(Error::User { explanation: _ })))
    }

    #[test]
    fn parse_short() {
        let result: Result<BackupPassword, Error> = "abcd".parse();
        assert!(matches!(result, Err(Error::User { explanation: _ })))
    }

    #[test]
    fn parse_long() {
        let result: Result<BackupPassword, Error> =
            "8FD93-EYWZR-GB7HX-QAVNS-QAVNS".parse();
        assert!(matches!(result, Err(Error::User { explanation: _ })))
    }
}
