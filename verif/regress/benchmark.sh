# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon (guillaume.chauvon@thalesgroup.com)

# where are the tools
if [ -z "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh

source ./verif/sim/setup-env.sh

if [ -z "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-testharness,spike
fi

if [ -z "$DV_TARGET" ]; then
  DV_TARGET=cv64a6_imafdc_sv39
fi

cd verif/sim/

BDIR=../tests/riscv-tests/benchmarks/
CVA6_FLAGS="--target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --linker ../tests/custom/common/test.ld"

GCC_COMMON_SRC=(
        ../tests/riscv-tests/benchmarks/common/syscalls.c
        ../tests/riscv-tests/benchmarks/common/crt.S
)

GCC_CFLAGS=(
        -fno-tree-loop-distribute-patterns
        -static
        -mcmodel=medany
        -fvisibility=hidden
        -nostdlib
        -nostartfiles
        -lgcc
        -O3 --no-inline
        -I../tests/custom/env
        -I../tests/custom/common
        -DNOPRINT
)

GCC_OPTS="${GCC_CFLAGS[*]} ${GCC_COMMON_SRC[*]}"

python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/dhrystone/dhrystone.c   --gcc_opts "$GCC_OPTS -I$BDIR/dhrystone/    $BDIR/dhrystone/dhrystone_main.c"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/median/median.c         --gcc_opts "$GCC_OPTS -I$BDIR/median/       $BDIR/median/median_main.c"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/mm/mm.c                 --gcc_opts "$GCC_OPTS -I$BDIR/mm/           $BDIR/mm/mm_main.c"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/mt-matmul/mt-matmul.c   --gcc_opts "$GCC_OPTS -I$BDIR/mt-matmul/    $BDIR/mt-matmul/matmul.c"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/mt-vvadd/mt-vvadd.c     --gcc_opts "$GCC_OPTS -I$BDIR/mt-vvadd/     $BDIR/mt-vvadd/vvadd.c"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/multiply/multiply.c     --gcc_opts "$GCC_OPTS -I$BDIR/multiply/     $BDIR/multiply/multiply_main.c"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/pmp/pmp.c               --gcc_opts "$GCC_OPTS -I$BDIR/pmp/"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/qsort/qsort_main.c      --gcc_opts "$GCC_OPTS -I$BDIR/qsort/"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/rsort/rsort.c           --gcc_opts "$GCC_OPTS -I$BDIR/rsort/"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/spmv/spmv_main.c        --gcc_opts "$GCC_OPTS -I$BDIR/spmv/"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/towers/towers_main.c    --gcc_opts "$GCC_OPTS -I$BDIR/towers/"
python3 cva6.py $CVA6_FLAGS --c_tests $BDIR/vvadd/vvadd.c           --gcc_opts "$GCC_OPTS -I$BDIR/vvadd/        $BDIR/vvadd/vvadd_main.c"

make clean
make -C verif/sim clean_all

cd -

