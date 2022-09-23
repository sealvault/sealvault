// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::{async_runtime as rt, Error};
use http_cache_reqwest::{CACacheManager, Cache, CacheMode, HttpCache};
use reqwest::{Client, Response};
use reqwest_middleware::{ClientBuilder, ClientWithMiddleware};
use std::fmt::Debug;

#[derive(Debug)]
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

    /// Get urls concurrently.
    /// The request library wants owned urls.
    fn get_all(
        &self,
        urls: impl Iterator<Item = url::Url>,
    ) -> Result<Vec<Result<Response, HttpClientError>>, Error> {
        let tasks = urls.map(|url| rt::spawn(self.client.get(url).send()));
        let tasks = rt::block_on(futures::future::join_all(tasks));
        let mut responses: Vec<Result<Response, HttpClientError>> = Default::default();
        for task in tasks {
            // Propagate join error if any.
            let middleware_result = task?;
            let response: Result<Response, HttpClientError> = middleware_result
                // Turn the response into HTTP error if any, then convert reqwuest error to
                // middleware error if any.
                .and_then(|r| r.error_for_status().map_err(|err| err.into()))
                // Convert middleware error to HttpClientError if any.
                .map_err(|err| err.into());
            responses.push(response);
        }
        Ok(responses)
    }
}

// Trait helps with mocking for tests
pub trait GetAllBytes {
    /// Fetch bodies as bytes concurrently.
    fn get_bytes(
        &self,
        urls: impl Iterator<Item = url::Url>,
    ) -> Result<Vec<Result<Vec<u8>, HttpClientError>>, Error>;
}

impl GetAllBytes for HttpClient {
    fn get_bytes(
        &self,
        urls: impl Iterator<Item = url::Url>,
    ) -> Result<Vec<Result<Vec<u8>, HttpClientError>>, Error> {
        let responses = self.get_all(urls)?;
        let results = responses
            .into_iter()
            .map(|r| {
                r.and_then(|r| {
                    rt::block_on(r.bytes())
                        .map(|r| r.to_vec())
                        .map_err(|err| err.into())
                })
            })
            .collect();
        Ok(results)
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
