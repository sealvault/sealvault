// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::http_client::{GetAllBytes, HttpClientError};
use crate::{config, Error};

use url::{Host, Url};

/// Fetch favicons for a list of urls concurrently from the DuckDuckGo favicon api.
/// Uses local cache.
/// Returns the favicons as png, or a fallback if failed to fetch.
pub fn fetch_favicons(
    client: &impl GetAllBytes,
    urls: impl IntoIterator<Item = Url>,
) -> Result<Vec<Option<Vec<u8>>>, Error> {
    let mut api_urls: Vec<Url> = Default::default();
    for url in urls {
        api_urls.push(site_url_to_api_url(url)?);
    }
    let responses = client.get_bytes(api_urls.into_iter())?;
    let mut result: Vec<Option<Vec<u8>>> = Default::default();
    for response in responses {
        let favicon: Option<Vec<u8>> = match response {
            Ok(favicon) => Some(favicon),
            Err(HttpClientError::Core { error }) => {
                // Propagate core error
                Err(error)?
            }
            // In case of middleware or reqwuest error, fetch fallback.
            _error => None,
        };
        result.push(favicon)
    }
    Ok(result)
}

fn site_url_to_api_url(url: Url) -> Result<Url, Error> {
    let domain = match url.host() {
        Some(Host::Domain(domain)) => domain,
        // Will return fallback image
        _ => "none",
    };
    let api = format!("{}{}.ico", config::FAVICON_API, domain);
    Url::parse(&api).map_err(|err| Error::Fatal {
        // Parse errors dont' contain the url, OK to include in error.
        error: format!("Failed to parse API URL: '{}'", err),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    use url::Url;

    struct MockHttpClient {}

    impl GetAllBytes for MockHttpClient {
        fn get_bytes(
            &self,
            urls: impl Iterator<Item = Url>,
        ) -> std::result::Result<Vec<Result<Vec<u8>, HttpClientError>>, Error> {
            let result: Vec<Result<Vec<u8>, HttpClientError>> = urls
                .map(|_| {
                    let body: Vec<u8> = Default::default();
                    let response =
                        http::Response::builder().status(500).body(body).unwrap();
                    let response: reqwest::Response = response.into();
                    let error = response.error_for_status().err().unwrap();
                    Err(HttpClientError::Request { error })
                })
                .collect();
            Ok(result)
        }
    }

    #[test]
    fn none_on_request_error() -> Result<()> {
        let urls: Vec<Url> = vec![
            "https://app.uniswap.org/#/swap?chain=mainnet",
            "https://app.ens.domains/",
        ]
        .iter()
        .map(|s| Url::parse(s).unwrap())
        .collect();
        let count = urls.len();
        let client = MockHttpClient {};
        let results = fetch_favicons(&client, urls)?;
        assert_eq!(results.len(), count);
        for res in results {
            assert!(res.is_none())
        }

        Ok(())
    }

    #[test]
    fn dapp_url_to_api_url_expected() -> Result<()> {
        let url = site_url_to_api_url(
            Url::parse("https://example.com/foo/bar?baz=fubar#frag").unwrap(),
        )?;
        let expected_url =
            Url::parse("https://icons.duckduckgo.com/ip3/example.com.ico").unwrap();
        assert_eq!(url, expected_url);
        Ok(())
    }

    #[test]
    fn no_panic_on_domain_edge_cases() -> Result<()> {
        let url = site_url_to_api_url(
            Url::parse("https://example.com/foo/bar?baz=fubar#frag").unwrap(),
        )?;
        let expected_url =
            Url::parse("https://icons.duckduckgo.com/ip3/example.com.ico").unwrap();
        assert_eq!(url, expected_url);
        Ok(())
    }
}
