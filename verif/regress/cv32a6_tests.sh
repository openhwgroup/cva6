#!/bin/bash
# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi


# install the required tools
source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh

# install the required test suites
source ./verif/regress/install-riscv-compliance.sh
source ./verif/regress/install-riscv-tests.sh
source ./verif/regress/install-riscv-arch-test.sh

# setup sim env
source ./verif/sim/setup-env.sh

echo "$SPIKE_INSTALL_DIR$"

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-testharness,spike
fi

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv32a65x
fi

if ! [ -n "$UVM_VERBOSITY" ]; then
  export UVM_VERBOSITY=UVM_NONE
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"

cd verif/sim/

errors=0

# 32-bit configurations without MMU
riscv_tests_list=(
  rv32ui-p-add
  rv32ui-p-lw
  rv32ui-p-sw
  rv32ui-p-beq
  rv32ui-p-jal
)
for t in ${riscv_tests_list[@]} ; do
  python3 cva6.py --testlist=../tests/testlist_riscv-tests-${DV_TARGET}-p.yaml --test $t --iss_yaml cva6.yaml --target ${DV_TARGET} --iss=$DV_SIMULATORS $DV_OPTS
  [[ $? > 0 ]] && ((errors++))
done

python3 cva6.py --target ${DV_TARGET} --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/hello_world/hello_world.c --linker=../tests/custom/common/test.ld\
  --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -lgcc -I../tests/custom/env -I../tests/custom/common" $DV_OPTS
[[ $? > 0 ]] && ((errors++))

make -C ../.. clean
make clean_all

[[ $errors > 0 ]] && exit 1 ;
exit 0 ;
