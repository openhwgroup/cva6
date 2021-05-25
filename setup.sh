#!/bin/bash

export PATH=/scratch/lvalente/riscv_install/bin:$PATH

export RISCV=/scratch/lvalente/riscv_install

export QUESTASIM_HOME=/usr/pack/modelsim-10.7b-kgf/questasim/

###riscv64-unknown-elf-gcc -mcmodel=medany -static -std=gnu99 -O2 -ffast-math -fno-common -fno-builtin-printf -T /scratch/lvalente/project/ariane-soc/tmp/riscv-tests/benchmarks/common/test.ld  -static -nostdlib -nostartfiles -lm -lgcc /scratch/lvalente/project/ariane-soc/tmp/riscv-tests/benchmarks/common/crt.S /scratch/lvalente/project/ariane-soc/tmp/riscv-tests/benchmarks/common/syscalls.c -L /scratch/lvalente/project/ariane-soc/tmp/riscv-tests/benchmarks/common hello.c -o hello.riscv
