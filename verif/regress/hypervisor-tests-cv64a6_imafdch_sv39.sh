# Copyright 2021 Thales DIS design services SAS
# Inria 2026
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales
# Modified by Nicolas Derumigny - Inria

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-testharness,spike
fi

# install the required tools
if [[ "$DV_SIMULATORS" == *"veri-testharness"* ]]; then
  source ./verif/regress/install-verilator.sh
fi
source ./verif/regress/install-spike.sh

# install the required test suites
source ./verif/regress/install-riscv-compliance.sh
source ./verif/regress/install-riscv-tests.sh
source ./verif/regress/install-riscv-arch-test.sh

# setup sim env
source ./verif/sim/setup-env.sh

echo "$SPIKE_INSTALL_DIR$"

if ! [ -n "$UVM_VERBOSITY" ]; then
    export UVM_VERBOSITY=UVM_NONE
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"

CC_OPTS="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -lgcc -D__riscv_cbo"


cd verif/sim/

srcs=(
    ../tests/custom/rvh/main_timer.c
    ../tests/custom/rvh/main_u.c
    ../tests/custom/rvh/main_vs.c
    ../tests/custom/rvh/main_satp.c
    ../tests/custom/rvh/main_vsatp.c
    ../tests/custom/rvh/main_hgatp.c
)
srcA=(
    ../tests/custom/rvh/call.c
    ../tests/custom/rvh/mmode.c
    ../tests/custom/rvh/page_table.s
    ../tests/custom/rvh/tests.c
    ../tests/custom/rvh/trampoline.S
    ../tests/custom/rvh/utils.c
    ../tests/custom/rvh/vm.c
)

for src in "${srcs[@]}"; do
    python3 cva6.py --c_tests $src --iss_yaml cva6.yaml --compare_outputs --no_ecall_exit --target cv64a6_imafdch_sv39 --iss=$DV_SIMULATORS --gcc_opts="${srcA[*]} $CC_OPTS" $DV_OPTS --linker=../tests/custom/rvh/main.ld
done

cd -
