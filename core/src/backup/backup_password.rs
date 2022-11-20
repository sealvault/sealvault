// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashSet, str::FromStr};

use lazy_static::lazy_static;
use rand::Rng;
use subtle::ConstantTimeEq;
use zeroize::ZeroizeOnDrop;

use crate::Error;

const PASSWORD_LENGTH: usize = 20;

const INVARIANT_VIOLATION: &str = "Invariant violation";

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

#[derive(ZeroizeOnDrop)]
pub struct BackupPassword(Vec<u8>);

impl BackupPassword {
    fn new(password: Vec<u8>) -> Result<Self, Error> {
        let default: [u8; PASSWORD_LENGTH] = Default::default();
        if password.len() != PASSWORD_LENGTH || password.ct_eq(&default).unwrap_u8() == 1
        {
            return Err(Error::Fatal {
                error: INVARIANT_VIOLATION.into(),
            });
        }
        Ok(Self(password))
    }

    #[allow(dead_code)]
    pub fn random() -> Result<Self, Error> {
        let mut rng = rand::thread_rng();

        let mut password: Vec<u8> = Vec::with_capacity(PASSWORD_LENGTH);
        for _ in 0..PASSWORD_LENGTH {
            // No fallible interface for gen_range unfortunately. It should panic if insufficient
            // entropy, but not guaranteed.
            let abc_index = rng.gen_range(0..ALPHABET.len());
            password.push(ALPHABET[abc_index]);
        }

        BackupPassword::new(password)
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
            let slice = &self.0[start..end];
            for c in slice {
                res.push(*c as char)
            }
            if i < dashes - 1 {
                res.push('-')
            }
        }
        res
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
        let mut password: Vec<u8> = Vec::with_capacity(PASSWORD_LENGTH);
        for c in s.chars() {
            if let Some(symbol) = decode_symbol(c) {
                // Symbols in the character set are guaranteed to fit into u8.
                password.push(symbol as u8)
            }
        }
        if password.len() != PASSWORD_LENGTH {
            return Err(Error::User {
                explanation: "Invalid password length".to_string(),
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
}
