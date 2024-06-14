# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Zbigniew CHAMSKI (zbigniew.chamski@thalesgroup.fr)

noprint=""
if [ "$1" == "--no-print" ]; then
        noprint="-DHAS_PRINTF=0"
fi

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
  DV_SIMULATORS=veri-testharness
fi

if ! [ -n "$UVM_VERBOSITY" ]; then
    export UVM_VERBOSITY=UVM_NONE
fi

make clean
make -C verif/sim clean_all

cd verif/sim/

src0=../tests/custom/coremark/core_main.c
srcA=(
        ../tests/custom/coremark/uart.c
        ../tests/custom/coremark/core_list_join.c
        ../tests/custom/coremark/core_matrix.c
        ../tests/custom/coremark/core_portme.c
        ../tests/custom/coremark/core_state.c
        ../tests/custom/coremark/core_util.c
        ../tests/custom/common/syscalls.c
        ../tests/custom/common/crt.S
)

cflags_opt=(
        -O3 -g
        -fno-tree-loop-distribute-patterns
        -static
        -mcmodel=medany
        -fvisibility=hidden
        -nostdlib
        -nostartfiles
        -lgcc
        $noprint
        -funroll-all-loops
        -ffunction-sections -fdata-sections
        -Wl,-gc-sections
        -falign-jumps=4 -falign-functions=16
)

cflags=(
        "${cflags_opt[@]}"
        "-DCOMPILER_FLAGS='\"${cflags_opt[*]}\"'"
        -DITERATIONS=2
        -DPERFORMANCE_RUN
        -DSKIP_TIME_CHECK
        -I../tests/custom/env
        -I../tests/custom/common
        -DNOPRINT
)

default_config="cv32a65x"
isa="rv32imc_zba_zbb_zbc_zbs"

set -x
python3 cva6.py \
        --target hwconfig \
        --isa "$isa" \
        --hwconfig_opts="$default_config" \
        --iss="$DV_SIMULATORS" \
        --iss_yaml=cva6.yaml \
        --c_tests "$src0" \
        --gcc_opts "${srcA[*]} ${cflags[*]}" \
        --linker ../tests/custom/common/test.ld \
        $DV_OPTS
