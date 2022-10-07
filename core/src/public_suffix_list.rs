// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{
    fmt::{Debug, Formatter},
    str,
    time::Duration,
};

use publicsuffix::Psl;

use crate::{assets::load_asset_as_string, config, Error};

/// Represents list of domain suffixes under which internet users can directly register domains
/// names. See https://publicsuffix.org/ for more.
pub struct PublicSuffixList {
    list: publicsuffix::List,
}

impl PublicSuffixList {
    pub fn new() -> Result<Self, Error> {
        let list_text = Self::load_bundled_psl()?;
        let list: publicsuffix::List =
            list_text
                .parse()
                .map_err(|err: publicsuffix::Error| Error::Fatal {
                    error: err.to_string(),
                })?;
        Ok(Self { list })
    }

    fn load_bundled_psl() -> Result<String, Error> {
        let list = load_asset_as_string(config::PUBLIC_SUFFIX_LIST_ASSET)?;
        Ok(list)
    }

    pub fn registrable_domain(
        &self,
        origin: &url::Origin,
    ) -> Result<RegistrableDomain, Error> {
        match origin {
            url::Origin::Tuple(_, host, _) => self.registrable_domain_for_host(host),
            url::Origin::Opaque(_) => Ok(RegistrableDomain::Null),
        }
    }

    fn registrable_domain_for_host(
        &self,
        host: &url::Host,
    ) -> Result<RegistrableDomain, Error> {
        match host {
            url::Host::Domain(ref domain) => {
                let registrable_domain: Option<&[u8]> = self
                    .list
                    .domain(domain.as_bytes())
                    .map(|val| val.as_bytes());
                Ok(match registrable_domain {
                    Some(val) => RegistrableDomain::Domain(str::from_utf8(val)?.into()),
                    None => RegistrableDomain::Null,
                })
            }
            _ => Ok(RegistrableDomain::Null),
        }
    }
}

impl Debug for PublicSuffixList {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PublicSuffixList")
            .field("list", &self.list)
            .finish()
    }
}

/// Lets us mock remote updater at test time.
trait ListUpdater: Send + Sync {
    fn new(cache_dir: String) -> Self
    where
        Self: Sized;
    fn needs_update(&self) -> bool;
    fn poll_frequency(&self) -> Duration;
    fn fetch_public_suffix_list(&self) -> Result<String, Error>;
}

/// Wrapper type for safety.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RegistrableDomain {
    Null,
    Domain(String),
}

impl RegistrableDomain {
    /// Whether the registrable domain exists.
    pub fn exists(&self) -> bool {
        matches!(*self, RegistrableDomain::Domain(_))
    }
}

impl From<RegistrableDomain> for Option<String> {
    fn from(rd: RegistrableDomain) -> Self {
        match rd {
            RegistrableDomain::Null => None,
            RegistrableDomain::Domain(s) => Some(s),
        }
    }
}

impl<'a> From<&'a RegistrableDomain> for Option<&'a str> {
    fn from(rd: &'a RegistrableDomain) -> Self {
        match rd {
            RegistrableDomain::Null => None,
            RegistrableDomain::Domain(s) => Some(s),
        }
    }
}

impl From<Option<String>> for RegistrableDomain {
    fn from(opt: Option<String>) -> Self {
        match opt {
            None => Self::Null,
            Some(s) => Self::Domain(s),
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use lazy_static::lazy_static;

    use super::*;

    fn rd(s: &str) -> RegistrableDomain {
        RegistrableDomain::Domain(s.into())
    }

    lazy_static! {
        static ref TEST_CASES: Vec<(&'static str, RegistrableDomain)> =
            vec![
            // URL WHATWG spec test vectors
            // From https://url.spec.whatwg.org/#host-registrable-domain
            ("com", RegistrableDomain::Null),
            ("example.com", rd("example.com")),
            ("www.example.com", rd("example.com")),
            ("sub.www.example.com", rd("example.com")),
            ("EXAMPLE.COM", rd("example.com")),
            // FQDN
            ("example.com.", rd("example.com.")),
            ("github.io", RegistrableDomain::Null),
            ("whatwg.github.io", rd("whatwg.github.io")),
            ("إختبار", RegistrableDomain::Null),
            ("example.إختبار", rd("example.xn--kgbechtv")),
            ("sub.example.إختبار", rd("example.xn--kgbechtv")),
            ("[2001:0db8:85a3:0000:0000:8a2e:0370:7334]", RegistrableDomain::Null),

            // FQDN TLD
            (".", RegistrableDomain::Null),

            // Localhost
            ("localhost", RegistrableDomain::Null),
            ("127.0.0.1", RegistrableDomain::Null),

        ];
    }

    /// Implementation can panic. Only for tests.
    impl Default for PublicSuffixList {
        fn default() -> Self {
            Self::new().unwrap()
        }
    }

    #[test]
    fn psl_not_empty() -> Result<()> {
        let psl: PublicSuffixList = Default::default();

        assert!(!psl.list.is_empty());

        Ok(())
    }

    #[test]
    fn test_vectors() -> Result<()> {
        let psl: PublicSuffixList = Default::default();

        for (host, expected) in TEST_CASES.clone().into_iter() {
            let host = url::Host::<String>::parse(host)?;

            assert_eq!(psl.registrable_domain_for_host(&host)?, expected);
        }

        Ok(())
    }
}
