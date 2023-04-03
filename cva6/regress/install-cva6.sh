# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

# Customise this to a fast local disk
export ROOT_PROJECT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../" && pwd)
export TOP=$ROOT_PROJECT/tools

# where to install the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install Verilator
# Use historical variable VERILATOR_ROOT to check/specify VL configuration.
if [ -z "$VERILATOR_ROOT" ]; then
  # Verilator installation dir should be separate from the VL source root.
  # Source code will be unpacked, built and tested in the 'verilator'
  # subdir of the install dir.
  export VERILATOR_ROOT=$TOP/verilator-5.008/verilator
fi

# If the installation directory of Verilator is not set,
# default to the parent directory of the Verilator source.
if [ -z "$VERILATOR_INSTALL_DIR" ]; then
  export VERILATOR_INSTALL_DIR=$(dirname $VERILATOR_ROOT)
fi
cva6/regress/install-verilator.sh

# With Verilator v5, it is (FORNOW) necessary to either maintain a copy
# of the source+build directory at $VERILATOR_ROOT, or to unset VERILATOR_ROOT
# so that 'verilator_bin' is searched in the PATH.  The former is not
# applicable to Continuous Integration environments, so...
unset VERILATOR_ROOT

export PATH=$RISCV/bin:$VERILATOR_INSTALL_DIR/bin:$PATH
export LIBRARY_PATH=$RISCV/lib
export LD_LIBRARY_PATH=$RISCV/lib
export C_INCLUDE_PATH=$RISCV/include:$VERILATOR_INSTALL_DIR/share/verilator/include
export CPLUS_INCLUDE_PATH=$RISCV/include:$VERILATOR_INSTALL_DIR/share/verilator/include

# Check proper Verilator installation given current $PATH.
echo PATH=\"$PATH\"
echo "Verilator version:"
verilator --version

# number of parallel jobs to use for make commands and simulation
export NUM_JOBS=24

# install the required tools for cva6
if ! [ -n "$CVA6_REPO" ]; then
  CVA6_REPO="https://github.com/openhwgroup/cva6.git"
  CVA6_BRANCH="master"
  CVA6_HASH="75807530f26ba9a0ca501e9d3a6575ec375ed7ab"
  CVA6_PATCH=
fi
echo $CVA6_REPO
echo $CVA6_BRANCH
echo $CVA6_HASH
echo $CVA6_PATCH

if ! [ -d core-v-cores/cva6 ]; then
  git clone --recursive $CVA6_REPO -b $CVA6_BRANCH core-v-cores/cva6
  cd core-v-cores/cva6; git checkout $CVA6_HASH;
  echo -n "Using CVA6 commit "; git describe --always HEAD
  if [ -f ../$CVA6_PATCH ]; then
    git apply ../$CVA6_PATCH
  fi
  cd -
fi

# install Spike
if ! [ -n "$SPIKE_ROOT" ]; then
  export SPIKE_ROOT=$TOP/spike/
fi
cva6/regress/install-spike.sh
