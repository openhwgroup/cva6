# Copyright 2024 CoreLab Tech
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/

noprint=""
if [ "$1" == "--no-print" ]; then
        noprint="-DHAS_PRINTF=0"
fi

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

source ./verif/sim/setup-env.sh

DV_SIMULATORS=vcs-uvm

if ! [ -n "$UVM_VERBOSITY" ]; then
    export UVM_VERBOSITY=UVM_NONE
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+UVM_VERBOSITY=$UVM_VERBOSITY"
export DV_OPTS="$DV_OPTS --issrun_opts=+mem_vp_enabled=1"

make clean
make -C verif/sim clean_all

cd verif/sim/

src0=../tests/custom/debug_test/debug_test.c
srcA=(
        ../tests/custom/debug_test/debugger_exception.S
        ../tests/custom/debug_test/debugger.S
        ../tests/custom/debug_test/handlers.S
        ../tests/custom/debug_test/single_step.S
        ../tests/custom/debug_test/trigger_code.S
        ../tests/custom/debug_test/bsp/crt0.S
        ../tests/custom/debug_test/bsp/syscalls.c
        ../tests/custom/debug_test/bsp/vectors.S
)

cflags_opt=(
  -mabi=ilp32 \
  -march=rv32imac_zicsr_zifencei \
  -Os -g -static -Wall -pedantic  \
  -nostartfiles \
  -Wunused-variable \
  -mno-relax
)

cflags=(
        "${cflags_opt[@]}"
        "-DCOMPILER_FLAGS='\"${cflags_opt[*]}\"'"
        -I../tests/custom/debug_test/
        -I../tests/custom/debug_test/bsp
)

default_target="cv32a6_imac_sv0"

link_ld="../tests/custom/debug_test/bsp/link.ld"

set -x
python3 cva6.py \
        --target "$default_target" \
        --iss="$DV_SIMULATORS" \
        --iss_yaml=cva6.yaml \
        --c_tests "$src0" \
        --gcc_opts "${srcA[*]} ${cflags[*]}" \
        --linker "$link_ld" \
        $DV_OPTS -v
