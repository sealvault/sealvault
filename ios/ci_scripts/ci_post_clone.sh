#!/bin/sh

set -e

brew install rustup-init
rustup-init -y --default-toolchain nightly

