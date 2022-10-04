#!/usr/bin/env python3
"""Run builds, linters and tests.
"""

from pathlib import Path
import subprocess as sp
import signal


DEV_SERVER_PROCESS = None
REPO_ROOT = Path(__file__).parent
DEV_SERVER_DIR = REPO_ROOT / "tools/dev-server"
IOS_DIR = REPO_ROOT / "ios"


def main():
    mpl_header_check()
    run_clippy()
    # Platform specific code only gets linted when compiled for that target.
    run_clippy("aarch64-apple-ios")

    run_rust_tests()

    start_dev_server()
    run_ios_ui_tests()


def cleanup():
    if DEV_SERVER_PROCESS is not None:
        print("Killing dev server process")
        DEV_SERVER_PROCESS.kill()


def signal_handler(signum, frame):
    print("Signal handler called with signal", signum)
    cleanup()


def start_dev_server():
    global DEV_SERVER_PROCESS

    DEV_SERVER_PROCESS = sp.Popen(["cargo", "run"], cwd=DEV_SERVER_DIR)


def mpl_header_check():
    pattern = """
^// This Source Code Form is subject to the terms of the Mozilla Public$
^// License, v. 2.0. If a copy of the MPL was not distributed with this$
^// file, You can obtain one at https://mozilla.org/MPL/2.0/.$
    """.strip()
    # Current directory at end is important otherwise fails in GitHub CI
    command = f'rg --files-without-match --multiline -trust -tswift -tjs "{pattern}" ./'
    result = sp.run(command, capture_output=True, shell=True, text=True)
    # 0 means match and 1 means no match which is what we want
    if result.returncode > 1:
        print("rg returned failed with error", result.returncode)
        print(result.stderr)
        exit(result.returncode)

    if result.stdout:
        print("Linter error. All source files must start with the MPL header:")
        regex_chars = dict.fromkeys(map(ord, '^$'), None)
        print(pattern.translate(regex_chars))
        print("The following files are missing the header:")
        print(result.stdout)
        exit(1)


def run_clippy(target=None):
    target_arg = f"--target {target} " if target else ""
    # The first two rules are disabled to regressions in clippy that produce false positives:
    # https://github.com/rust-lang/rust-clippy/issues/8867
    # https://github.com/rust-lang/rust-clippy/issues/9014
    allow = "-A clippy::derive_partial_eq_without_eq -A clippy::extra_unused_lifetimes"

    sp.run(
        f"cargo clippy {target_arg}-- -D warnings {allow}".split(" "),
        check=True,
    )


def run_rust_tests():
    sp.run(["cargo", "test", "--package", "sealvault_core"], check=True)


def run_ios_ui_tests():
    sp.run(["fastlane", "tests"], check=True, cwd=IOS_DIR)


if __name__ == "__main__":
    # Finally block is not enough in case another interrupt is received
    # while it's executing.
    signal.signal(signal.SIGINT, signal_handler)

    try:
        main()
    finally:
        cleanup()

    print("Success")
