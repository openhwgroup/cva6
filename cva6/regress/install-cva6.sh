# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

# Customise this to a fast local disk
export ROOT_PROJECT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../" && pwd)
export TOP=$ROOT_PROJECT/tools

# where to install the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install Verilator
if ! [ -n "$VERILATOR_ROOT" ]; then
  export VERILATOR_ROOT=$TOP/verilator-4.110/
fi
cva6/regress/install-verilator.sh

export PATH=$RISCV/bin:$VERILATOR_ROOT/bin:$PATH
export LIBRARY_PATH=$RISCV/lib
export LD_LIBRARY_PATH=$RISCV/lib
export C_INCLUDE_PATH=$RISCV/include:$VERILATOR_ROOT/include
export CPLUS_INCLUDE_PATH=$RISCV/include:$VERILATOR_ROOT/include

# number of parallel jobs to use for make commands and simulation
export NUM_JOBS=24

# install the required tools for cva6
if ! [ -n "$CVA6_REPO" ]; then
  CVA6_REPO="https://github.com/openhwgroup/cva6.git"
  CVA6_BRANCH="master"
  CVA6_HASH="bb9821d85f88d4e615bfa9bb35c9a78ed6f0b579"
  CVA6_PATCH=
fi
echo $CVA6_REPO
echo $CVA6_BRANCH
echo $CVA6_HASH
echo $CVA6_PATCH

if ! [ -d core-v-cores/cva6 ]; then
  git clone --recursive $CVA6_REPO -b $CVA6_BRANCH core-v-cores/cva6
  cd core-v-cores/cva6; git checkout $CVA6_HASH;
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
