#!/bin/sh

set -e

export PATH="${PATH}:${HOME}/.cargo/bin/"
# We only use Xcode Cloud for release builds
python3 "${CI_WORKSPACE}/ios/pre_build.py" --configuration release
