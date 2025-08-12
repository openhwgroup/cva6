#!/bin/bash
# Copyright 2025 Isaar AHMAD
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Isaar AHMAD
#
# ==============================================================================
# This script installs RISCV proxy kernel at ${ROOT_PROJECT}/tools/pk,
# where ROOT_PROJECT is base of the CVA6 repository.
# ==============================================================================
set -e # Exit immediately if a command fails

PK_ARCH=$1
PK_MABI=$2
PK_REPO="https://github.com/riscv-software-src/riscv-pk.git"
PK_BRANCH="master"
PK_COMMIT_HASH="e5563d1044bd6790325c4602c49f89e1182fa91a"

if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return 1
fi

PATH=$RISCV/bin:$PATH
# Customise this to a fast local disk
ROOT_PROJECT=$(readlink -f $(dirname "${BASH_SOURCE[0]}")/../../)

if [ -z "$NUM_JOBS" ]; then
    NUM_JOBS=1
fi

# Unset historical variable PK_ROOT as it collides with the build process.
if [ -n "$PK_ROOT" ]; then
  unset PK_ROOT
fi

echo "[install-pk.sh] Entry values:"
echo "    PK_BUILD_DIR='$PK_BUILD_DIR'"
echo "    PK_INSTALL_DIR='$PK_INSTALL_DIR'"

# If not set, define the installation location of pk to the local path
#
#    <top>/tools/pk
#
# Continuous Integration may need to override this particular variable
# to use a preinstalled build of Verilator.
if [ -z "$PK_INSTALL_DIR" ]; then
  export PK_INSTALL_DIR="$ROOT_PROJECT/tools/pk"
  echo "Setting PK_INSTALL_DIR to '$PK_INSTALL_DIR'..."
fi

# Define the default src+build location of pk in case it needs to be (re)built.
# No need to force this location in Continuous Integration scripts.
if [ -z "$PK_BUILD_DIR" ]; then
  export PK_BUILD_DIR="$PK_INSTALL_DIR/build-pk"
  echo "Setting PK_BUILD_DIR to '$PK_BUILD_DIR'..."
fi

# Clean previous installation directory to ensure a fresh install
echo "Cleaning old installation directory: $PK_INSTALL_DIR"
rm -rf "$PK_INSTALL_DIR"

# Build and install pk only if the final binary is not present.
# Note: The script now always rebuilds due to the rm -rf above.
if [ ! -f "$PK_INSTALL_DIR/riscv-none-elf/bin/pk" ]; then
    echo "Building pk in '$PK_BUILD_DIR'..."
    echo "pk will be installed in '$PK_INSTALL_DIR'"
    echo "PK_REPO=$PK_REPO"
    echo "PK_COMMIT_HASH=$PK_COMMIT_HASH"
    echo "NUM_JOBS=$NUM_JOBS"

    mkdir -p "$PK_BUILD_DIR"
    pushd "$PK_BUILD_DIR"
    # Fetch repository only if the ".git" directory does not exist.
    # Do not remove the content arbitrarily if ".git" does not exist in order
    # to preserve user content - let git fail instead.
    if [ ! -d ".git" ]; then
        echo "Cloning full repository from ${PK_REPO}..."
        git clone "${PK_REPO}" .
    else
        echo "Repository already exists. Fetching updates..."
        git fetch origin
    fi

    echo "Checking out commit: ${PK_COMMIT_HASH}"
    git checkout "${PK_COMMIT_HASH}"

    # Proceed with the build
    mkdir -p build
    pushd build
    ../configure --prefix="$PK_INSTALL_DIR" --host=riscv-none-elf --with-arch="$PK_ARCH"
    make -j${NUM_JOBS}
    make install
    popd # build
    popd # $PK_BUILD_DIR
else
    echo "pk already installed in '$PK_INSTALL_DIR'."
fi

# Add pk bin directory to PATH if not already present.
echo "$PATH" | grep -q "$PK_INSTALL_DIR/bin:" || \
  export PATH="$PK_INSTALL_DIR/bin:$PATH"

echo "Successfully configured RISC-V Proxy Kernel."
