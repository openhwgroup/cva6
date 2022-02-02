# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

# riscv-dv env variables
export RISCV_TOOLCHAIN=$RISCV
if ! [ -n "$RISCV_GCC" ]; then
  export RISCV_GCC="$RISCV_TOOLCHAIN/bin/riscv-none-elf-gcc"
fi
if ! [ -n "$RISCV_OBJCOPY" ]; then
  export RISCV_OBJCOPY="$RISCV_TOOLCHAIN/bin/riscv-none-elf-objcopy"
fi
export SPIKE_PATH=$SPIKE_ROOT/bin
export RTL_PATH=$ROOT_PROJECT/core-v-cores/cva6
export TB_PATH=$ROOT_PROJECT/cva6/tb/core
export TESTS_PATH=$ROOT_PROJECT/cva6/tests

if ! [ -n "$DV_REPO" ]; then
  export DV_REPO="https://github.com/google/riscv-dv.git"
  export DV_BRANCH=master
  export DV_HASH=0ce85d3187689855cd2b3b9e3fae21ca32de2248
  export DV_PATCH=
fi
echo $DV_REPO
echo $DV_BRANCH
echo $DV_HASH
echo $DV_PATCH

mkdir -p cva6/sim
if ! [ -d cva6/sim/dv ]; then
  git clone $DV_REPO -b $DV_BRANCH cva6/sim/dv
  cd cva6/sim/dv; git checkout $DV_HASH;
  if [ -f "$DV_PATCH" ]; then
    git apply $DV_PATCH
  fi
  cd -
fi

# install riscv-dv dependencies
cd cva6/sim/dv; pip3 install -r requirements.txt; cd -
