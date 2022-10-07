// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::str::FromStr;

use diesel::r2d2;
use jsonrpsee::types::error::ErrorCode as JsonrpseeErrorCode;
use lazy_static::lazy_static;
use regex::Regex;

#[derive(Debug, PartialEq, thiserror::Error)]
pub enum Error {
    #[error("Jsonrpc error code: {code} message:\n {message}")]
    JsonRpc {
        code: JsonrpseeErrorCode,
        message: String,
    },
    /// The operation resulted in an error, but it can be retried.
    #[error("Retriable Error: '{error}'")]
    Retriable { error: String },
    /// A runtime invariant violation.
    /// The error will be sent to Sentry, so it should not contain any user data.
    #[error("Fatal Error: '{error}'")]
    Fatal { error: String },
    /// Errors that user can make and we want to want to explain to them what's wrong.
    /// The explanation can be presented directly to the user.
    #[error("{explanation}")]
    User { explanation: String },
}

// We don't use anyhow for `UnexpectedError` in order to have a single place where
// all possible runtime invariant variations are listed.
// TODO (abiro) add macro to derive `UnexpectedError` default implementations.

impl From<r2d2::PoolError> for Error {
    fn from(err: r2d2::PoolError) -> Self {
        Error::Fatal {
            error: err.to_string(),
        }
    }
}

impl From<diesel::result::Error> for Error {
    fn from(err: diesel::result::Error) -> Self {
        const SQLITE_BUSY_MESSAGE: &str = "database is locked";

        match err {
            diesel::result::Error::DatabaseError(kind, info) => {
                if info.message() == SQLITE_BUSY_MESSAGE {
                    Error::Retriable {
                        error: "Failed to acquire DB lock in busy_timeout.".to_string(),
                    }
                } else {
                    Error::Fatal {
                        // Don't include `DatabaseErrorInformation` as it can contain user data.
                        error: format!(
                            "Unexpected Diesel database error kind: '{:?}'",
                            kind
                        ),
                    }
                }
            }
            _ => Error::Fatal {
                error: err.to_string(),
            },
        }
    }
}

impl From<base64::DecodeError> for Error {
    fn from(_: base64::DecodeError) -> Self {
        Error::Fatal {
            error: "Invalid base64 string".into(),
        }
    }
}

impl From<std::str::Utf8Error> for Error {
    fn from(_: std::str::Utf8Error) -> Self {
        Error::Fatal {
            error: "Invalid UTF-8 bytes".into(),
        }
    }
}

impl From<aead::Error> for Error {
    fn from(err: aead::Error) -> Self {
        Error::Fatal {
            // Opaque error, OK to expose
            error: err.to_string(),
        }
    }
}

impl From<k256::pkcs8::der::Error> for Error {
    fn from(err: k256::pkcs8::der::Error) -> Self {
        Error::Fatal {
            // Opaque error, OK to expose
            error: err.to_string(),
        }
    }
}

impl From<k256::elliptic_curve::Error> for Error {
    fn from(err: k256::elliptic_curve::Error) -> Self {
        Error::Fatal {
            // Opaque error, OK to expose
            error: err.to_string(),
        }
    }
}

impl From<ecdsa::Error> for Error {
    fn from(err: ecdsa::Error) -> Self {
        Error::Fatal {
            // Opaque error, OK to expose
            error: err.to_string(),
        }
    }
}

impl From<k256::pkcs8::spki::Error> for Error {
    fn from(err: k256::pkcs8::spki::Error) -> Self {
        Error::Fatal {
            // Opaque error, OK to expose
            error: err.to_string(),
        }
    }
}

impl<T> From<std::sync::PoisonError<T>> for Error {
    fn from(err: std::sync::PoisonError<T>) -> Self {
        Error::Fatal {
            error: err.to_string(),
        }
    }
}

impl From<tokio::task::JoinError> for Error {
    fn from(err: tokio::task::JoinError) -> Self {
        Error::Fatal {
            error: err.to_string(),
        }
    }
}

impl From<jsonrpsee::core::Error> for Error {
    fn from(err: jsonrpsee::core::Error) -> Self {
        let error: jsonrpsee::types::ErrorObjectOwned = err.into();
        error.into()
    }
}

impl From<url::ParseError> for Error {
    fn from(err: url::ParseError) -> Self {
        Error::Retriable {
            // Error is opaque, OK to expose.
            error: err.to_string(),
        }
    }
}

lazy_static! {
    static ref ETHERS_JSONRPC_ERROR_CODE_REGEX: Regex =
        Regex::new(r"\(code: (?P<code>-?\d+),").unwrap();
}

// This is a hack to get around the Ethers-rs provider returning opaque JSON-RPC client errors
// and errors needing a static lifetime for downcasting: https://stackoverflow.com/a/48062162
fn parse_eth_json_rpc_error(error_display: &str) -> Option<JsonrpseeErrorCode> {
    ETHERS_JSONRPC_ERROR_CODE_REGEX
        .captures(error_display)
        .and_then(|captures| captures.name("code"))
        .and_then(|code| <i32 as FromStr>::from_str(code.as_str()).ok())
        .map(|code| code.into())
}

impl From<ethers::providers::ProviderError> for Error {
    fn from(err: ethers::providers::ProviderError) -> Self {
        use ethers::providers::ProviderError;
        match err {
            ProviderError::JsonRpcClientError(message) => {
                let error_display = message.to_string();
                if let Some(error_code) = parse_eth_json_rpc_error(&error_display) {
                    Self::JsonRpc {
                        code: error_code,
                        message: error_display,
                    }
                } else {
                    Error::Retriable {
                        error: error_display,
                    }
                }
            }
            ProviderError::EnsError(message) => Error::User {
                explanation: message,
            },
            err => Error::Retriable {
                error: err.to_string(),
            },
        }
    }
}

impl ethers::providers::FromErr<ethers::providers::ProviderError> for Error {
    fn from(err: ethers::providers::ProviderError) -> Self {
        err.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_jronsrpc_client_error() {
        let display = "(code: -32000, message: transaction underpriced, data: None)";
        let code = parse_eth_json_rpc_error(display);
        assert_eq!(code.unwrap(), JsonrpseeErrorCode::ServerError(-32000))
    }

    #[test]
    fn no_panic_on_unexpected_jsonrpc_message() {
        let display = "something unexpected 123";
        let code = parse_eth_json_rpc_error(display);
        assert_eq!(code, None)
    }
}
