#!/bin/bash
# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales
#
# Contributor: Cesar Fuguet, CEA List
# RISC-V tests for 64-bit configurations implementing MMU

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
  DV_TARGET=cv64a6_imafdc_sv39_hpdcache
fi

if ! [ -n "$UVM_VERBOSITY" ]; then
  export UVM_VERBOSITY=UVM_NONE
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"

cd verif/sim/

errors=0

# 64-bit configurations implementing MMU
riscv_tests_list=(
  rv64ui-v-add
  rv64ui-v-ld
  rv64ui-v-sd
  rv64ui-v-beq
  rv64ui-v-jal
)
for t in ${riscv_tests_list[@]} ; do
  python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-v.yaml --test $t --iss_yaml cva6.yaml --target ${DV_TARGET} --iss=$DV_SIMULATORS $DV_OPTS
  [[ $? > 0 ]] && ((errors++))
done

python3 cva6.py --target ${DV_TARGET} --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/hello_world/hello_world.c \
  --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -T ../tests/custom/common/test.ld" $DV_OPTS
[[ $? > 0 ]] && ((errors++))

make -C ../.. clean
make clean_all

[[ $errors > 0 ]] && exit 1 ;
exit 0 ;
