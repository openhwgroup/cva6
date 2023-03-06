# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

if ! [ -n "$RISCV_ISA_SIM" ]; then
  RISCV_ISA_SIM="https://github.com/riscv-software-src/riscv-isa-sim.git"
  RISCV_ISA_SIM_BRANCH="master"
  RISCV_ISA_SIM_HASH="b9fc8e4e9087a6064dfcc627efabbe3fd4bdc309"
  RISCV_ISA_SIM_PATCH="../../../cva6/regress/riscv-isa-sim.patch"
fi
echo $RISCV_ISA_SIM
echo $RISCV_ISA_SIM_BRANCH
echo $RISCV_ISA_SIM_HASH
echo $RISCV_ISA_SIM_PATCH

if ! [ -d cva6/tests/riscv-isa-sim ]; then
  git clone $RISCV_ISA_SIM -b $RISCV_ISA_SIM_BRANCH cva6/tests/riscv-isa-sim
  cd cva6/tests/riscv-isa-sim; git checkout $RISCV_ISA_SIM_HASH;
  if [ -f "$RISCV_ISA_SIM_PATCH" ]; then
    git apply $RISCV_ISA_SIM_PATCH
  fi
  cd -
fi

