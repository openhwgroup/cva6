# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon (guillaume.chauvon@thalesgroup.com)

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-uvm
fi

# install the required tools
if [[ "$DV_SIMULATORS" == *"veri-testharness"* ]]; then
  source ./verif/regress/install-verilator.sh
fi
source ./verif/regress/install-spike.sh

source ./verif/sim/setup-env.sh

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv32a65x
fi

make clean
make -C verif/sim clean_all

cd verif/sim

srcA=(
        ../tests/custom/common/syscalls.c
        ../tests/custom/common/crt.S
)
cflags=(
        -static
        -mcmodel=medany
        -fvisibility=hidden
        -nostartfiles
        -Oz -fno-inline
        -Wno-implicit-function-declaration
        -Wno-implicit-int
        -I../tests/custom/env
        -I../tests/custom/common
        -I../tests/custom/dhrystone/
        -DNOPRINT
)

python3 cva6.py \
        --target "$DV_TARGET" \
        --hwconfig_opts="$DV_HWCONFIG_OPTS" \
        --iss="$DV_SIMULATORS" \
        --iss_yaml=cva6.yaml \
        --c_tests "../tests/custom/return0/return0.c" \
        --gcc_opts "${srcA[*]} ${cflags[*]}"

cd -
