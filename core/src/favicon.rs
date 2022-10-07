// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::iter;

use url::{Host, Url};

use crate::{async_runtime as rt, config, http_client::HttpClient, Error};

/// Fetch favicons for a list of urls concurrently from the DuckDuckGo favicon api.
/// Uses local cache and returns None if there was an error fetching the favicon.
pub async fn fetch_favicons_async(
    client: &HttpClient,
    urls: impl IntoIterator<Item = Url>,
) -> Result<Vec<Option<Vec<u8>>>, Error> {
    let mut api_urls: Vec<Url> = Default::default();
    for url in urls {
        api_urls.push(site_url_to_api_url(url)?);
    }
    let results = client.get_bytes(api_urls.into_iter()).await;
    Ok(results)
}

/// Fetch favicons for a list of urls concurrently from the DuckDuckGo favicon api.
/// Uses local cache and returns None if there was an error fetching the favicon.
pub fn fetch_favicons(
    client: &HttpClient,
    urls: impl IntoIterator<Item = Url>,
) -> Result<Vec<Option<Vec<u8>>>, Error> {
    rt::block_on(fetch_favicons_async(client, urls))
}

/// Fetch one favicon from the DuckDuckGo favicon api.
/// Uses local cache and returns None if there was an error fetching the favicon.
pub async fn fetch_favicon_async(
    client: &HttpClient,
    url: Url,
) -> Result<Option<Vec<u8>>, Error> {
    let results = fetch_favicons_async(client, iter::once(url)).await?;
    let first = results.into_iter().next().flatten();
    Ok(first)
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
    use anyhow::Result;
    use url::Url;

    use super::*;

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
