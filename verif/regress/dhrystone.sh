# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Zbigniew CHAMSKI (zbigniew.chamski@thalesgroup.fr)

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh
source verif/regress/install-riscv-compliance.sh
source verif/regress/install-riscv-tests.sh

source ./verif/sim/setup-env.sh

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-uvm
fi

if ! [ -n "$DV_HWCONFIG_OPTS" ]; then
  DV_HWCONFIG_OPTS="cv32a65x"
fi

make clean
make -C verif/sim clean_all

cd verif/sim

src0=../tests/custom/dhrystone/dhrystone_main.c
srcA=(
        ../tests/custom/dhrystone/dhrystone.c
        ../tests/custom/common/syscalls.c
        ../tests/custom/common/crt.S
)
cflags=(
        -fno-tree-loop-distribute-patterns
        -static
        -mcmodel=medany
        -fvisibility=hidden
        -nostdlib
        -nostartfiles
        -lgcc
        -O3 --no-inline
        -Wno-implicit-function-declaration
        -Wno-implicit-int
        -I../tests/custom/env
        -I../tests/custom/common
        -I../tests/custom/dhrystone/
        -DNOPRINT
)

python3 cva6.py \
        --target hwconfig \
        --hwconfig_opts="$DV_HWCONFIG_OPTS" \
        --iss="$DV_SIMULATORS" \
        --iss_yaml=cva6.yaml \
        --c_tests "$src0" \
        --issrun_opts="+tb_performance_mode" \
        --gcc_opts "${srcA[*]} ${cflags[*]}"
