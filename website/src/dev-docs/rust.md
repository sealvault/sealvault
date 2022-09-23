# Rust Code Guidelines

## Why Rust

We need a cross-platform key and transaction management component upon which
platform-specific UIs can be built. We chose Rust for this component because of
memory safety, low level control over key buffers, cross-platform portability
and good blockchain library support. Rust is the only programming language that
satisfies all these requirements.

Our Rust code is exposed to host languages that implement the app UIs via
[uniffi-rs](https://github.com/mozilla/uniffi-rs).


## Performance

Good performance of Rust code is desired, but it’s not a deal-breaker. We
prioritize maintainability and agility over performance. In other words, feel
free to clone stuff if it lets you ship features quicker or if it significantly
reduces code complexity.

We are particularly weary to introduce any optimizations at this time, as we’ll
have to introduce generic blockchain traits as we add support for more protocols
(we currently only support Ethereum), and performance optimizations in Rust
sometimes lead to rather unwieldy generics.

## Concurrency

Since we are using [uniffi-rs](https://github.com/mozilla/uniffi-rs) to expose
Rust to host languages via FFI, we have two options to deal with concurrent
operations:

1. Make FFI calls non-blocking, do async in Rust, and pass results through
callback interfaces to host languages.  
2. Make FFI calls blocking and let the host languages deal with concurrency.

The second option is simpler for both the Rust and the UI code, since the host
languages (Swift and Kotlin at this point) have good concurrency primitives that
UI developers are familiar with (as opposed to a custom callback scheme), and
async Rust has some rough edges which we can avoid this way.  For this reason,
our Rust code is written as single threaded, blocking code and concurrency is
handled by the host languages. 

There are two exceptions:

1. Some of our Rust dependencies only expose async interfaces. In this case we
block on them with the `async_runtime` module that wraps a lazy-initialized
global Tokio runtime.
2. Since we have an async runtime anyway for our dependencies, if there is a
function that we want to call multiple times concurrently during one FFI call
(eg. to fetch multiple images), then we write that function as async, spawn
instances of it on the async runtime and then block on the joined futures.
