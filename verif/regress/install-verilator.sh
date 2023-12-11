# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

if [ -z "$NUM_JOBS" ]; then
    NUM_JOBS=1
fi

# Ensure the location of tools is known (usually, .../core-v-verif/tools).
if [ -z "$TOP" ]; then
  echo "Error: location of core-v-verif 'tools' tree (\$TOP) is not defined."
  return
fi

VERILATOR_REPO="https://github.com/verilator/verilator.git"
VERILATOR_BRANCH="master"
# Use the release tag instead of a full SHA1 hash.
VERILATOR_HASH="v5.008"
VERILATOR_PATCH="$TOP/../verif/regress/verilator-v5.patch"

# Unset historical variable VERILATOR_ROOT as it collides with the build process.
if [ -n "$VERILATOR_ROOT" ]; then
  unset VERILATOR_ROOT
fi

# Define the default src+build location of Verilator.
# No need to force this location in Continuous Integration scripts.
if [ -z "$VERILATOR_BUILD_DIR" ]; then
  export VERILATOR_BUILD_DIR=${TOP}/verilator-$VERILATOR_HASH/verilator
fi

# Define the default installation location of Verilator: one level up
# from the source tree in the core-v-verif tree.
# Continuous Integration may need to override this particular variable
# to use a preinstalled build of Verilator.
if [ -z "$VERILATOR_INSTALL_DIR" ]; then
  export VERILATOR_INSTALL_DIR="$(dirname $VERILATOR_BUILD_DIR)"
fi

# Build and install Verilator only if not already installed at the expected
# location $VERILATOR_INSTALL_DIR.
if [ ! -f "$VERILATOR_INSTALL_DIR/bin/verilator" ]; then
    echo "Building Verilator in $VERILATOR_BUILD_DIR..."
    echo "Verilator will be installed in $VERILATOR_INSTALL_DIR"
    echo "VERILATOR_REPO=$VERILATOR_REPO"
    echo "VERILATOR_BRANCH=$VERILATOR_BRANCH"
    echo "VERILATOR_HASH=$VERILATOR_HASH"
    echo "VERILATOR_PATCH=$VERILATOR_PATCH"
    echo "NUM_JOBS=$NUM_JOBS"
    mkdir -p $VERILATOR_BUILD_DIR
    cd $VERILATOR_BUILD_DIR
    # Clone only if the ".git" directory does not exist.
    # Do not remove the content arbitrarily if ".git" does not exist in order
    # to preserve user content - let git fail instead.
    [ -d .git ] || git clone $VERILATOR_REPO -b $VERILATOR_BRANCH .
    git checkout $VERILATOR_HASH
    if [[ -n "$VERILATOR_PATCH" && -f "$VERILATOR_PATCH" ]] ; then
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

# Update PATH to match the verilator installation.
export PATH="$VERILATOR_INSTALL_DIR/bin:$PATH"

