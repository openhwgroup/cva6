# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

set -e

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

VERILATOR_REPO="https://github.com/verilator/verilator.git"
VERILATOR_BRANCH="master"
# Use the release tag instead of a full SHA1 hash.
VERILATOR_HASH="v5.008"
VERILATOR_PATCH="../../../cva6/regress/verilator-v5.patch"

# VERILATOR_ROOT must point to the root of the Verilator source tree.
# This is not necessarily the installation prefix.
# The two should be kept separate ==> use VERILATOR_INSTALL_DIR to specify
# the installation location of Verilator.
if [ ! -f "$VERILATOR_INSTALL_DIR/bin/verilator" ]; then
    echo "Building Verilator in $VERILATOR_ROOT..."
    echo "Verilator will be installed in $VERILATOR_INSTALL_DIR"
    echo "VERILATOR_REPO=$VERILATOR_REPO"
    echo "VERILATOR_BRANCH=$VERILATOR_BRANCH"
    echo "VERILATOR_HASH=$VERILATOR_HASH"
    echo "VERILATOR_PATCH=$VERILATOR_PATCH"
    mkdir -p $VERILATOR_ROOT
    cd $VERILATOR_ROOT
    # Clone only if the ".git" directory does not exist.
    # Do not remove the content arbitrarily if ".git" does not exist in order
    # to preserve user content - let git fail instead.
    [ -d .git ] || git clone $VERILATOR_REPO -b $VERILATOR_BRANCH .
    git checkout $VERILATOR_HASH
    if [ ! -z "$VERILATOR_PATCH" ] ; then
      git apply $VERILATOR_PATCH || true
    fi
    # Generate the config script and configure Verilator.
    autoconf && ./configure --prefix="$VERILATOR_INSTALL_DIR" && make -j${NUM_JOBS}
    # FORNOW: Accept failure in 'make test' (segfault issue on Debian10)
    make test || true
    echo "Installing Verilator in $VERILATOR_INSTALL_DIR..."
    make install
    #make test || echo "### 'make test' in $VERILATOR_ROOT: some tests failed."
    cd -
else
    echo "Using Verilator from cached directory $VERILATOR_INSTALL_DIR."
fi
