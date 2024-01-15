#!/bin/bash
# Copyright 2021-2023 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

if [ -z ${NUM_JOBS} ]; then
  NUM_JOBS=1
fi

ROOT_PROJECT=$(readlink -f $(dirname "${BASH_SOURCE[0]}")/../..)

# Set the location of Spike source code.
# Use the in-tree vendorized Spike if SPIKE_SRC_DIR is not set
# or when a fully local installation was requested.
if [ -z "$SPIKE_SRC_DIR" -o "$SPIKE_INSTALL_DIR" = "__local__" ]; then
  SPIKE_SRC_DIR=$ROOT_PROJECT/verif/core-v-verif/vendor/riscv/riscv-isa-sim
fi

# Expect/perform Spike installation in directory $SPIKE_INSTALL_DIR.
# which defaults to $ROOT_PROJECT/tools/spike.
if [ -z "$SPIKE_INSTALL_DIR" -o "$SPIKE_INSTALL_DIR" = "__local__" ]; then
  SPIKE_INSTALL_DIR="$ROOT_PROJECT/tools/spike"
fi

# Do not clean up the destination directory: leave that to the user (real or CI job).

# Rebuild Spike or reuse an existing Spike build.
if ! [ -f "$SPIKE_INSTALL_DIR/bin/spike" ]; then
  echo "Building Spike in $SPIKE_SRC_DIR"
  echo "Installing Spike in $SPIKE_INSTALL_DIR"
  # Keep track of current working dir.
  CALLER_DIR="$(pwd)"
  # Enter the vendorized tree.  It already captures the desired Spike config.
  cd $SPIKE_SRC_DIR
  echo "Building Spike sources in $SPIKE_SRC_DIR..."
  # Build and install Spike (including extensions).
  mkdir -p build
  cd build
  if [[ ! -f config.log ]]; then
      ../configure --prefix="$SPIKE_INSTALL_DIR"
  fi
  make -j${NUM_JOBS}
  echo "Installing Spike in '$SPIKE_INSTALL_DIR'..."
  sudo make install
  cd $CALLER_DIR
else
  echo "Spike already installed in '$SPIKE_INSTALL_DIR'."
fi
