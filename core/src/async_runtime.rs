// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

#[cfg(not(feature = "without_global_executor"))]
use lazy_static::lazy_static;
use std::future::Future;
use tokio::task::JoinHandle;

#[cfg(not(feature = "without_global_executor"))]
use crate::config;

#[cfg(not(feature = "without_global_executor"))]
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

#[cfg(not(feature = "without_global_executor"))]
/// Execute async code synchronously.
///
/// We have to provide synchronous interfaces for FFI, but many of our dependencies expose async
/// interfaces. We convert them to sync with this function.
pub fn block_on<F: Future>(future: F) -> F::Output {
    RUNTIME.block_on(future)
}

#[cfg(not(feature = "without_global_executor"))]
pub fn spawn<T>(future: T) -> JoinHandle<T::Output>
where
    T: Future + Send + 'static,
    T::Output: Send + 'static,
{
    RUNTIME.spawn(future)
}

#[cfg(not(feature = "without_global_executor"))]
/// Runs the provided function on an executor dedicated to blocking operations.
pub fn spawn_blocking<F, R>(f: F) -> JoinHandle<R>
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    RUNTIME.spawn_blocking(f)
}

#[cfg(not(feature = "without_global_executor"))]
/// Get a handle to the runtime.
pub fn handle() -> tokio::runtime::Handle {
    RUNTIME.handle().clone()
}

/// We need this for the Actix dev server that has its own runtime which is neither configurable,
/// nor is it possible to get a reference to it.
#[cfg(feature = "without_global_executor")]
pub fn block_on<F: Future>(future: F) -> F::Output {
    let rt = tokio::runtime::Handle::current();
    rt.block_on(future)
}

#[cfg(feature = "without_global_executor")]
pub fn spawn<T>(future: T) -> JoinHandle<T::Output>
where
    T: Future + Send + 'static,
    T::Output: Send + 'static,
{
    let rt = tokio::runtime::Handle::current();
    rt.spawn(future)
}

#[cfg(feature = "without_global_executor")]
pub fn spawn_blocking<F, R>(f: F) -> JoinHandle<R>
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    let rt = tokio::runtime::Handle::current();
    rt.spawn_blocking(f)
}

#[cfg(feature = "without_global_executor")]
/// Get a handle to the runtime.
pub fn handle() -> tokio::runtime::Handle {
    tokio::runtime::Handle::current()
}
