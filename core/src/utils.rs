// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{collections::HashSet, time::SystemTime};

use chacha20poly1305::aead::generic_array::{ArrayLength, GenericArray};
use chrono::{DateTime, FixedOffset, SecondsFormat, Utc};
use email_address::EmailAddress;
use lazy_static::lazy_static;
use rand::{thread_rng, RngCore};
use url::Url;
use uuid::Uuid;

use crate::Error;

/// Create an RFC339 timestamp, eg.: "2018-01-26T18:30:09.453Z".
/// From: https://stackoverflow.com/a/64148017
pub fn rfc3339_timestamp() -> String {
    let now = SystemTime::now();
    let dt: DateTime<Utc> = now.into();
    dt.to_rfc3339_opts(SecondsFormat::Millis, true)
}

pub fn parse_rfc3339_timestamp(s: &str) -> Result<DateTime<FixedOffset>, Error> {
    DateTime::parse_from_rfc3339(s).map_err(|err| Error::Retriable {
        error: err.to_string(),
    })
}

/// Number of seconds since unix epoch
pub fn unix_timestamp() -> i64 {
    let dt: DateTime<Utc> = SystemTime::now().into();
    dt.timestamp()
}

/// Generate a new v4 UUID.
pub fn new_uuid() -> String {
    Uuid::new_v4().to_string()
}

// Minimum secure length for random bytes (128 bit).
const MIN_RANDOM_BYTES_LENGTH: usize = 16;

pub fn try_fill_random_bytes(buffer: &mut [u8]) -> Result<(), Error> {
    // This is most likely a logic error and potentially dangerous. It can happen for example that
    // the buffer has 0 length when passing a vector created with a capacity, but not filled yet.
    if buffer.len() < MIN_RANDOM_BYTES_LENGTH {
        return Err(Error::Fatal {
            error: "Insecure secret buffer length.".into(),
        });
    }
    let mut rng = thread_rng();
    rng.try_fill_bytes(buffer).map_err(|err| Error::Fatal {
        error: format!(
            "Failed to generate random bytes with error code: {:?}",
            err.code()
        ),
    })?;
    Ok(())
}

/// Generate cryptographically secure random bytes for a generic array.
/// Fails if the OS random generator fails.
pub fn try_random_bytes<N: ArrayLength<u8>>() -> Result<GenericArray<u8, N>, Error> {
    let mut buffer: GenericArray<u8, N> = GenericArray::default();
    try_fill_random_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate cryptographically secure random bytes for a generic array.
/// Fails if the OS random generator fails.
pub fn blake3_hash<T: AsRef<[u8]>>(value: T) -> blake3::Hash {
    let mut hasher = blake3::Hasher::new();
    hasher.update(value.as_ref());
    hasher.finalize()
}

lazy_static! {
    static ref ALLOWED_SCHEMES: HashSet<&'static str> =
        ["http", "https", "file", "ftp",].into();
}

/// Turn a possible URI that a user typed into a browser address bar into a fully qualified URL.
/// Returns the URL if it's valid, else None.
/// Defaults to http if no scheme is specified to cover IP addresses as https upgrades are handled
/// elsewhere.
pub fn uri_fixup(input: impl AsRef<str>) -> Option<String> {
    let trimmed = input.as_ref().trim();

    // Quoted strings and email addresses should be passed on to search engine.
    if trimmed.contains('"') || EmailAddress::is_valid(trimmed) {
        return None;
    }

    let url = Url::parse(trimmed).or_else(|_| Url::parse(&format!("http://{}", trimmed)));

    url.ok().and_then(|u| {
        if !ALLOWED_SCHEMES.contains(u.scheme()) {
            return None;
        }

        if let Some(domain) = u.domain() {
            // If the domain has only one part and it's not localhost, we assume that it won't
            // resolve. This might cause problems in some development setups, or on networks that
            // make use of partially qualified domain names, but we cannot do better without doing
            // a DNS lookup.
            if domain != "localhost" && domain_part_count(domain) <= 1 {
                return None;
            }
        }

        let mut s = u.to_string();
        if s.ends_with('/') {
            s.pop();
        }
        Some(s)
    })
}

fn domain_part_count(domain: &str) -> usize {
    domain.split('.').filter(|s| !s.is_empty()).count()
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use chacha20poly1305::aead::generic_array::typenum::U32;

    use super::*;

    #[test]
    fn rfc_timestamp() -> Result<()> {
        let timestamp = rfc3339_timestamp();
        let _ = parse_rfc3339_timestamp(&timestamp)?;
        Ok(())
    }

    #[test]
    fn fills_random_bytes() -> Result<()> {
        const SIZE: usize = 32;
        let zeroes: Vec<u8> = vec![0; SIZE];

        let mut arr: Vec<u8> = vec![0; SIZE];
        try_fill_random_bytes(&mut arr)?;

        assert_ne!(arr, zeroes);
        assert_eq!(arr.len(), zeroes.len());

        Ok(())
    }

    #[test]
    fn random_bytes_is_not_default() -> Result<()> {
        type Array = GenericArray<u8, U32>;
        let default = Array::default();

        let rand_bytes: Array = try_random_bytes()?;

        assert_ne!(rand_bytes, default);
        assert_eq!(rand_bytes.len(), default.len());

        Ok(())
    }

    #[test]
    fn uri_fixup_cases() {
        fn ss(s: &str) -> Option<String> {
            Some(s.into())
        }

        // Test cases from: https://github.com/brave/brave-ios/blob/c93e42d0996039492a7b6b3783dad12574405dcb/Tests/ClientTests/SearchTests.swift

        // Check valid URLs. We can load these after some fixup.
        assert_eq!(
            uri_fixup("http://www.mozilla.org"),
            ss("http://www.mozilla.org")
        );
        // assert_eq!(url_fixup("about:"), ss("about:"));
        // assert_eq!(url_fixup("about:config"), ss("about:config"));
        // assert_eq!(url_fixup("about: config"), ss("about:%20config"));
        assert_eq!(uri_fixup("file:///f/o/o"), ss("file:///f/o/o"));
        assert_eq!(
            uri_fixup("ftp://ftp.mozilla.org"),
            ss("ftp://ftp.mozilla.org")
        );
        assert_eq!(uri_fixup("foo.bar"), ss("http://foo.bar"));
        assert_eq!(uri_fixup(" foo.bar "), ss("http://foo.bar"));
        // TODO failing case (strips port 80)
        // assert_eq!(uri_fixup("[::1]:80"), ss("http://[::1]:80"));
        assert_eq!(
            uri_fixup("[2a04:4e42:400::288]"),
            ss("http://[2a04:4e42:400::288]")
        );
        // TODO failing case (strips port 80)
        // assert_eq!(uri_fixup("[2a04:4e42:600::288]:80"), ss("http://[2a04:4e42:600::288]:80"));
        assert_eq!(
            uri_fixup("[2605:2700:0:3::4713:93e3]:443"),
            ss("http://[2605:2700:0:3::4713:93e3]:443")
        );
        // TODO failing cases (compresses to hex)
        // assert_eq!(uri_fixup("[::192.9.5.5]"), ss("http://[::192.9.5.5]"));
        // assert_eq!(uri_fixup("[::192.9.5.5]:80"), ss("http://[::192.9.5.5]:80"));
        // assert_eq!(uri_fixup("[::192.9.5.5]/png"), ss("http://[::192.9.5.5]/png"));
        // assert_eq!(uri_fixup("[::192.9.5.5]:80/png"), ss("http://[::192.9.5.5]:80/png"));
        assert_eq!(uri_fixup("192.168.2.1"), ss("http://192.168.2.1"));
        assert_eq!(uri_fixup("brave.io"), ss("http://brave.io"));
        assert_eq!(uri_fixup("brave.new.world"), ss("http://brave.new.world"));
        assert_eq!(
            uri_fixup("brave.new.world.test"),
            ss("http://brave.new.world.test")
        );
        assert_eq!(
            uri_fixup("brave.new.world.test.io"),
            ss("http://brave.new.world.test.io")
        );
        assert_eq!(
            uri_fixup("brave.new.world.test.whatever.io"),
            ss("http://brave.new.world.test.whatever.io")
        );
        // TODO failing case (converts to octets)
        // assert_eq!(uri_fixup("http://2130706433:8000/"), ss("http://2130706433:8000/"));
        assert_eq!(
            uri_fixup("http://127.0.0.1:8080"),
            ss("http://127.0.0.1:8080")
        );
        // TODO failing cases (expands to all octets)
        // assert_eq!(uri_fixup("http://127.0.1"), ss("http://127.0.1"));
        // assert_eq!(uri_fixup("http://127.1"), ss("http://127.1"));
        // assert_eq!(uri_fixup("http://127.1:8000"), ss("http://127.1:8000"));
        // assert_eq!(uri_fixup("http://1.1:80"), ss("http://1.1:80"));

        // Check invalid URLs. These are passed along to the default search engine.
        assert_eq!(uri_fixup("foobar"), None);
        assert_eq!(uri_fixup("foo bar"), None);
        assert_eq!(uri_fixup("mozilla. org"), None);
        // TODO failing case (parsed as IP address)
        // assert_eq!(uri_fixup("123"), None);
        assert_eq!(uri_fixup("a/b"), None);
        assert_eq!(uri_fixup("创业咖啡"), None);
        assert_eq!(uri_fixup("创业咖啡 中国"), None);
        assert_eq!(uri_fixup("创业咖啡. 中国"), None);
        assert_eq!(
            uri_fixup("data:text/html;base64,SGVsbG8gV29ybGQhCg=="),
            None
        );
        assert_eq!(
            uri_fixup("data://https://www.example.com,fake example.com"),
            None
        );
        // TODO failing cases (parsed as IP address)
        // assert_eq!(uri_fixup("1.2.3"), None);
        // assert_eq!(uri_fixup("1.1"), None);
        // assert_eq!(uri_fixup("127.1"), None);
        // assert_eq!(uri_fixup("127.1.1"), None);

        // Check invalid quoted URLs, emails, and quoted domains.
        // These are passed along to the default search engine.
        assert_eq!(uri_fixup(r#""123"#), None);
        assert_eq!(uri_fixup(r#""123""#), None);
        assert_eq!(uri_fixup(r#""ftp.mozilla.org"#), None);
        assert_eq!(uri_fixup(r#""ftp.mozilla.org""#), None);
        assert_eq!(uri_fixup(r#"https://"ftp.mozilla.org""#), None);
        assert_eq!(uri_fixup(r#"https://"ftp.mozilla.org"#), None);
        assert_eq!(uri_fixup("foo@brave.com"), None);
        assert_eq!(uri_fixup("\"foo@brave.com"), None);
        assert_eq!(uri_fixup("\"foo@brave.com\""), None);
        assert_eq!(uri_fixup(r#""创业咖啡.中国"#), None);
        assert_eq!(uri_fixup(r#""创业咖啡.中国""#), None);
        assert_eq!(uri_fixup("foo:5000"), None);
        assert_eq!(uri_fixup("http://::192.9.5.5"), None);
        assert_eq!(uri_fixup("http://::192.9.5.5:8080"), None);

        // Added for SealVault
        assert_eq!(uri_fixup("localhost"), ss("http://localhost"));
        assert_eq!(uri_fixup("http://localhost"), ss("http://localhost"));
        // TODO failing cases (returned with scheme)
        // assert_eq!(uri_fixup("localhost:8080/open-new-tab.html"), ss("http://localhost:8080/open-new-tab.html"));
        // assert_eq!(uri_fixup("localhost:1234"), ss("http://localhost:1234"));
        assert_eq!(
            uri_fixup("http://localhost:8080"),
            ss("http://localhost:8080")
        );
        assert_eq!(uri_fixup("https://example.com"), ss("https://example.com"));

        assert_eq!(uri_fixup("uniswap"), None);
    }
}
