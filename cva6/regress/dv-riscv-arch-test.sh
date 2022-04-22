# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

export RISCV_GCC=$RISCV/bin/riscv64-unknown-elf-gcc-10.2.0
export RISCV_OBJCOPY=$RISCV/riscv64-unknown-elf/bin/objcopy

export SPIKE_ROOT=$RISCV

#export CVA6_REPO=https://github.com/openhwgroup/cva6.git
#export CVA6_BRANCH=master
#export CVA6_HASH=34f63b44873148d371133bfa8642d2b7d388f39b

#export ARCH_TEST_REPO=https://github.com/riscv-non-isa/riscv-arch-test
#export ARCH_TEST_BRANCH=riscof-dev
#export ARCH_TEST_HASH=7907c462c700279c5d75ec5e6042f762dcb95a25

#export DV_REPO=https://github.com/google/riscv-dv.git
#export DV_BRANCH=master
#export DV_HASH=0ce85d3187689855cd2b3b9e3fae21ca32de2248

#export RISCV_ISA_SIM=https://github.com/riscv-software-src/riscv-isa-sim.git
#export RISCV_ISA_SIM_BRANCH=master
#export RISCV_ISA_SIM_HASH=b9fc8e4e9087a6064dfcc627efabbe3fd4bdc309

# install the required tools
source ./cva6/regress/install-cva6.sh
source ./cva6/regress/install-riscv-dv.sh
source ./cva6/regress/install-riscv-isa-sim.sh
source ./cva6/regress/install-riscv-arch-test.sh

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv64a6_imafdc_sv39
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-testharness,spike
fi

cd cva6/sim
python3 cva6.py --testlist=../tests/testlist_riscv-arch-test-$DV_TARGET.yaml --target $DV_TARGET --iss_yaml=cva6.yaml --iss=$DV_SIMULATORS $DV_OPTS
cd -
