// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use futures::StreamExt;
use http_cache_reqwest::{CACacheManager, Cache, CacheMode, HttpCache};
use reqwest::Client;
use reqwest_middleware::{ClientBuilder, ClientWithMiddleware};

use crate::{config, Error};

#[derive(Debug, Clone)]
pub struct HttpClient {
    client: ClientWithMiddleware,
}

impl HttpClient {
    pub fn new(cache_dir: String) -> Self {
        let client = ClientBuilder::new(Client::new())
            .with(Cache(HttpCache {
                mode: CacheMode::Default,
                manager: CACacheManager { path: cache_dir },
                options: None,
            }))
            .build();
        Self { client }
    }

    #[cfg(test)]
    pub fn new_without_cache() -> Self {
        let client = ClientBuilder::new(Client::new()).build();
        Self { client }
    }

    /// Fetch the URLs and return the bodies as bytes or None if there was an error.
    pub async fn get_bytes(
        &self,
        urls: impl Iterator<Item = url::Url>,
    ) -> Vec<Option<Vec<u8>>> {
        let result: Vec<Option<Vec<u8>>> = futures::stream::iter(urls)
            .map(|url| {
                let client = &self.client;
                async move {
                    // TODO log errors
                    let response = client.get(url).send().await.ok();
                    match response {
                        Some(response) => {
                            response.bytes().await.ok().map(|bytes| bytes.into())
                        }
                        None => None,
                    }
                }
            })
            .buffered(config::MAX_ASYNC_CONCURRENT_REQUESTS)
            .collect()
            .await;
        result
    }
}

#[derive(Debug, thiserror::Error)]
pub enum HttpClientError {
    // Intentionally opaque as request URL may contain sensitive info.
    #[error("Request error.")]
    Request { error: reqwest::Error },
    // Intentionally opaque as request URL may contain sensitive info.
    #[error("Middleware error.")]
    Middleware {
        // Middleware exposes anyhow
        error: anyhow::Error,
    },
    #[error("'{error}'")]
    Core { error: Error },
}

impl From<reqwest_middleware::Error> for HttpClientError {
    fn from(error: reqwest_middleware::Error) -> Self {
        match error {
            reqwest_middleware::Error::Reqwest(err) => err.into(),
            reqwest_middleware::Error::Middleware(error) => {
                HttpClientError::Middleware { error }
            }
        }
    }
}

impl From<reqwest::Error> for HttpClientError {
    fn from(error: reqwest::Error) -> Self {
        HttpClientError::Request { error }
    }
}

impl From<Error> for HttpClientError {
    fn from(error: Error) -> Self {
        HttpClientError::Core { error }
    }
}

impl From<tokio::task::JoinError> for HttpClientError {
    fn from(error: tokio::task::JoinError) -> Self {
        let error: Error = error.into();
        error.into()
    }
}
