#!/usr/bin/env python3
"""Build universal Rust binary from core and generate Swift bindings and templates.
"""

import argparse
from pathlib import Path
import shutil
import subprocess as sp
import tempfile
from unittest.loader import VALID_MODULE_NAME

CONFIGURATION_OPTIONS = set(["debug", "release"])

LIB_NAME = "sealvault_core"
SWIFT_FILE_NAME = "SealVaultCore"
XC_FRAMEWORK_NAME = f"{SWIFT_FILE_NAME}FFI"

# Multiple targets in the second dimension will be built into one framework with lipo
TARGETS = [
    # iOS
    ["aarch64-apple-ios"],
    # iOS simulator
    ["aarch64-apple-ios-sim", "x86_64-apple-ios"],
]

REPO_ROOT = Path(__file__).resolve().parents[1]

CORE_DIR = REPO_ROOT / "core"

IOS_DIR = REPO_ROOT / "ios"
SWIFT_SOURCES = IOS_DIR / "SealVaultApp"
SWIFT_GENERATED = SWIFT_SOURCES / "Generated"
SWIFT_TEMPLATES = SWIFT_SOURCES / "Templates"


def main(configuration, targets):
    flat_targets = []
    for lipo_targets in targets:
        flat_targets.extend(lipo_targets)

    work_dir = Path(tempfile.mkdtemp())

    if configuration != "debug":
        clean_rust()
    rust_targets_dir = build_rust(configuration, flat_targets)
    swift_generated_dir = generate_swift_bindings(work_dir)
    frameworks_dir = assemble_frameworks(
        work_dir=work_dir,
        rust_target_dir=rust_targets_dir,
        swift_bindings_dir=swift_generated_dir,
        configuration=configuration,
        targets=flat_targets,
    )
    xc_framework_dir = assemble_xcframework(work_dir, frameworks_dir, targets)

    clean_dir(SWIFT_GENERATED)
    move_results_to_repo(swift_generated_dir, xc_framework_dir)

    # Only remove the temporary directory on success to let developers inspect it on error
    shutil.rmtree(work_dir)


def clean_rust():
    sp.run(["cargo", "clean"], check=True, cwd=REPO_ROOT)


def build_rust(configuration, targets):
    args = ["cargo", "build"]
    if configuration != "debug":
        args.append("--release")
    for t in targets:
        target_args = args.copy()
        target_args.extend(["--target", t])
        sp.run(target_args, check=True, cwd=CORE_DIR)
    # We're using the default cargo target of workspace to share caches
    return REPO_ROOT / "target"


def generate_swift_bindings(work_dir):
    out_dir = work_dir / "swift-generated"
    udl_file = CORE_DIR / f"src/{SWIFT_FILE_NAME}.udl"
    uniffi_args = [
        "cargo",
        "uniffi-bindgen",
        "generate",
        str(udl_file),
        "--language",
        "swift",
        "--out-dir",
        str(out_dir),
    ]
    sp.run(uniffi_args, check=True, cwd=REPO_ROOT)

    module_file = out_dir / f"{XC_FRAMEWORK_NAME}.modulemap"
    replace_in_file(
        module_file,
        f"module {XC_FRAMEWORK_NAME}",
        f"framework module {XC_FRAMEWORK_NAME}",
    )

    return out_dir


def replace_in_file(file_path, from_str, to_str):
    text = file_path.read_text()
    new_text = text.replace(from_str, to_str)
    file_path.write_text(new_text)


def make_dirs(*args):
    for a in args:
        a.mkdir(parents=True)


def get_framework_dir(frameworks_dir, target):
    return frameworks_dir / f"{target}/{XC_FRAMEWORK_NAME}.framework"


def get_framework_lib_path(framework_dir):
    return framework_dir / XC_FRAMEWORK_NAME


def assemble_frameworks(
    work_dir, rust_target_dir, swift_bindings_dir, configuration, targets
):
    """Create an Xcode framework for each target."""

    frameworks_dir = work_dir / "frameworks"
    for target in targets:
        lib_file = rust_target_dir / f"{target}/{configuration}/libuniffi_{LIB_NAME}.a"

        fw_dir = get_framework_dir(frameworks_dir, target)
        headers_dir = fw_dir / "Headers"
        modules_dir = fw_dir / "Modules"

        make_dirs(headers_dir, modules_dir)

        shutil.copyfile(lib_file, get_framework_lib_path(fw_dir))

        header_file = swift_bindings_dir / f"{XC_FRAMEWORK_NAME}.h"
        shutil.copyfile(header_file, headers_dir / header_file.name)
        module_map_file = swift_bindings_dir / f"{XC_FRAMEWORK_NAME}.modulemap"
        shutil.copyfile(module_map_file, modules_dir / "module.modulemap")

    return frameworks_dir


def run_lipo(source_framework_dirs, output_framework_dir):
    args = ["lipo", "-create"]
    args.extend(map(get_framework_lib_path, source_framework_dirs))
    args.extend(["-output", get_framework_lib_path(output_framework_dir)])
    sp.run(args, check=True)


def assemble_xcframework(work_dir, frameworks_dir, targets):
    """Combine frameworks for different architectures into a single XCFramework."""
    out_dir = work_dir / f"{XC_FRAMEWORK_NAME}.xcframework"
    args = ["xcodebuild", "-create-xcframework", "-output", str(out_dir)]
    for lipo_targets in targets:
        target = lipo_targets[0]
        target_fw_dir = get_framework_dir(frameworks_dir, target)
        if len(lipo_targets) > 1:
            source_fws = list(
                map(lambda t: get_framework_dir(frameworks_dir, t), lipo_targets)
            )
            run_lipo(source_fws, target_fw_dir)
        args.extend(["-framework", str(target_fw_dir)])
    sp.run(args, check=True)
    return out_dir


def clean_dir(dir_path):
    shutil.rmtree(dir_path, ignore_errors=True)
    # Exists ok in case recreated by IDE between rmtree and creating it
    dir_path.mkdir(parents=True, exist_ok=True)


def move_results_to_repo(swift_generated_dir, xc_framework_dir):
    swift_file = swift_generated_dir / f"{SWIFT_FILE_NAME}.swift"
    shutil.copy(
        swift_file,
        SWIFT_GENERATED / swift_file.name,
    )

    xc_framework_destination = IOS_DIR / xc_framework_dir.name
    clean_dir(xc_framework_destination)
    shutil.copytree(xc_framework_dir, xc_framework_destination, dirs_exist_ok=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--configuration",
        type=str,
        default="debug",
        help="The build type",
    )
    args = parser.parse_args()

    configuration = args.configuration.lower()
    if configuration not in CONFIGURATION_OPTIONS:
        raise ValueError(
            f"Invalid configuration option: '{configuration}'. Choose one from: {CONFIGURATION_OPTIONS}"
        )

    main(configuration, TARGETS)
    print("success")
