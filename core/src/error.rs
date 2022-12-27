// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use diesel::r2d2;
use jsonrpsee::types::error::ErrorCode as JsonrpseeErrorCode;
use lazy_static::lazy_static;
use regex::Regex;

use crate::CoreError;

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
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
    /// An error where the message can be presented directly to the user.
    #[error("{explanation}")]
    User { explanation: String },
}

impl Error {
    pub fn message_for_ui_callback(self) -> String {
        // JSON-RPC errors are turned into user errors in CoreError if they're
        // presentable to users.
        let err: CoreError = self.into();
        match err {
            CoreError::User { explanation } => explanation,
            CoreError::Retriable { error } => {
                log::error!("Retriable error sending token: {error:?}");
                "An unexpected error occurred. Please try again!".into()
            }
            CoreError::Fatal { error } => {
                log::error!("Fatal error sending token: {error:?}");
                "An unexpected error occurred. Please restart the application and try again!".into()
            }
        }
    }
}

impl From<CoreError> for Error {
    fn from(error: CoreError) -> Self {
        match error {
            CoreError::Retriable { error } => Error::Retriable { error },
            CoreError::Fatal { error } => Error::Fatal { error },
            CoreError::User { explanation } => Error::User { explanation },
        }
    }
}

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
            // Error is opaque, ok to log.
            error: err.to_string(),
        }
    }
}

impl From<argon2::Error> for Error {
    fn from(err: argon2::Error) -> Self {
        Error::Fatal {
            // Error is opaque, ok to log.
            error: err.to_string(),
        }
    }
}

impl From<std::num::ParseIntError> for Error {
    fn from(err: std::num::ParseIntError) -> Self {
        Error::Retriable {
            // Error is opaque, ok to log.
            error: format!("Failed to parse int due to error: {err}"),
        }
    }
}

lazy_static! {
    static ref ETHERS_JSONRPC_CODE_REGEX: Regex =
        Regex::new(r"\(code: (?P<code>-?\d+),").expect("static is ok");
    static ref ETHERS_JSONRPC_MESSAGE_REGEX: Regex =
        Regex::new(r#"message: "?(?P<message>[\.:'!\?\-\d\w\s\+\*]+)"?,"#)
            .expect("static is ok");
}

// This is a hack to get around the Ethers-rs provider returning opaque JSON-RPC client errors
// and errors needing a static lifetime for downcasting: https://stackoverflow.com/a/48062162
fn parse_eth_json_rpc_error(error_display: &str) -> Option<(i32, Option<String>)> {
    let code: i32 = ETHERS_JSONRPC_CODE_REGEX
        .captures(error_display)?
        .name("code")?
        .as_str()
        .parse()
        .ok()?;
    if let Some(captures) = ETHERS_JSONRPC_MESSAGE_REGEX.captures(error_display) {
        let message = captures.name("message").map(|m| m.as_str().to_string());
        Some((code, message))
    } else {
        Some((code, None))
    }
}

impl From<ethers::providers::ProviderError> for Error {
    fn from(err: ethers::providers::ProviderError) -> Self {
        use ethers::providers::ProviderError;
        match err {
            ProviderError::JsonRpcClientError(error) => {
                let error_display = error.to_string();
                if let Some((code, message)) = parse_eth_json_rpc_error(&error_display) {
                    Self::JsonRpc {
                        code: code.into(),
                        message: message.unwrap_or(error_display),
                    }
                } else {
                    Self::Retriable {
                        error: error_display,
                    }
                }
            }
            ProviderError::EnsError(message) => Self::User {
                explanation: message,
            },
            err => Self::Retriable {
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
        let error = "(code: -32000, message: transaction underpriced, data: None)";
        let res = parse_eth_json_rpc_error(error);
        assert!(res.is_some());
        let (code, message) = res.unwrap();
        assert_eq!(code, -32000);
        assert_eq!(message, Some("transaction underpriced".into()));
    }

    #[test]
    fn parse_jronsrpc_client_error_with_asterisk() {
        let error = "(code: -32000, message: insufficient funds for gas * price + value, data: None)";
        let res = parse_eth_json_rpc_error(error);
        assert!(res.is_some());
        let (code, message) = res.unwrap();
        assert_eq!(code, -32000);
        assert_eq!(
            message,
            Some("insufficient funds for gas * price + value".into())
        );
    }

    #[test]
    fn no_panic_on_unexpected_jsonrpc_message() {
        let display = "something unexpected 123";
        let code = parse_eth_json_rpc_error(display);
        assert_eq!(code, None)
    }
}
