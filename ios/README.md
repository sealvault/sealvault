# SealVault iOS App

## Development 

Please refer to the [read me](../README.md) in the repo root for development 
setup instructions.

## Pre-Build

Before starting an Xcode build, a pre-build script needs to run to compile the
Rust [core source](../core) for iOS. You can run it with `fastlane pre_build`
from the `ios` directory. If the Rust core changes, you'll need to rerun this
script manually.

The pre-build script was originally part of the Xcode build in a "Run
Script" phase, but as it turns out, Xcode won't pick up changes to source files
from the run script phase in the same build run. This means that for every Rust
change we had to run Xcode build twice to be picked up in the iOS Simulator. So
now we just run it manually.

### Rust Core

The iOS app depends on shared functionality from the Rust [core](../core) for 
key and transaction management.

The Rust code is exposed via [uniffi-rs](https://github.com/mozilla/uniffi-rs)
to Swift. First, the Rust code is built into a multi-platform XCFramework with a
C interface and then a convenient Swift wrapper is generated and placed into
`SealVaultApp/Generated`. We need the multi-platform XCFramework for simulator
support.

## UI Tests

Prerequisite: the [dev-server](../tools/dev-server) must be running for browser
tests.

UI tests can be run from the `ios` directory with the `fastlane tests` command.
This command takes care of running the [pre-build](#pre-build) script, and it
also :warning: resets all iOS simulators on your machine.

Note that running the [CI script](../README.md#tests) locally also runs the UI
tests and takes care of starting and shutting down the
[dev-server](../tools/dev-server) for you.

## Linter

Run `swiftlint` with `fastlane lint` from the `ios` directory.

## Xcode Cloud

Xcode Cloud is used to automate TestFlight releases. A new TestFlight release 
is created for internal testers whenever a new tag with the `ios` prefix is 
pushed. These tags should follow the `ios-0.1.2` pattern.

## Useful Commands

### Find simulator database

```
fd sealvault-db.sqlite3  ~/Library/Developer/CoreSimulator/Devices/
```