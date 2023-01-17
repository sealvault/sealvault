// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::future::Future;

use lazy_static::lazy_static;
use tokio::task::JoinHandle;

use crate::config;

lazy_static! {
    static ref RUNTIME: tokio::runtime::Runtime = {
        tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .worker_threads(config::TOKIO_WORKER_THREADS)
            .max_blocking_threads(config::TOKIO_MAX_BLOCKING_THREADS)
            .build()
            .unwrap()
    };
}

/// Execute async code synchronously.
///
/// We have to provide synchronous interfaces for FFI, but many of our dependencies expose async
/// interfaces. We convert them to sync with this function.
pub fn block_on<F: Future>(future: F) -> F::Output {
    RUNTIME.block_on(future)
}

pub fn spawn<T>(future: T) -> JoinHandle<T::Output>
where
    T: Future + Send + 'static,
    T::Output: Send + 'static,
{
    RUNTIME.spawn(future)
}

/// Runs the provided function on an executor dedicated to blocking operations.
pub fn spawn_blocking<F, R>(f: F) -> JoinHandle<R>
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    RUNTIME.spawn_blocking(f)
}

/// Get a handle to the runtime.
pub fn handle() -> tokio::runtime::Handle {
    RUNTIME.handle().clone()
}
