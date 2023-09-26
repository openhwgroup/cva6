# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

# riscv-dv env variables
export RISCV_TOOLCHAIN=$RISCV
if [ -z "$RISCV_GCC" ]; then
  export RISCV_GCC="$RISCV_TOOLCHAIN/bin/riscv-none-elf-gcc"
fi
if [ -z "$RISCV_OBJCOPY" ]; then
  export RISCV_OBJCOPY="$RISCV_TOOLCHAIN/bin/riscv-none-elf-objcopy"
fi
export SPIKE_PATH=$SPIKE_INSTALL_DIR/bin
export RTL_PATH=$ROOT_PROJECT/
export TB_PATH=$ROOT_PROJECT/verif/tb/core
export TESTS_PATH=$ROOT_PROJECT/verif/tests

if [ -z "$DV_REPO" ]; then
  export DV_REPO="https://github.com/google/riscv-dv.git"
  export DV_BRANCH="master"
  export DV_HASH="96c1ee6f371f2754c45b4831fcab95f6671689d9"
  export DV_PATCH=
fi
echo "Repo:  " $DV_REPO
echo "Branch:" $DV_BRANCH
echo "Hash:  " $DV_HASH
echo "Patch: " $DV_PATCH

mkdir -p verif/sim
if ! [ -d verif/sim/dv ]; then
  git clone $DV_REPO -b $DV_BRANCH verif/sim/dv
  cd verif/sim/dv; git checkout $DV_HASH;
  if [[ -n "$DV_PATCH" && -f "$DV_PATCH" ]]; then
    git apply "$DV_PATCH"
  fi
  cd -
  # install riscv-dv dependencies
  cd verif/sim/dv; pip3 install -r requirements.txt; cd -
fi

