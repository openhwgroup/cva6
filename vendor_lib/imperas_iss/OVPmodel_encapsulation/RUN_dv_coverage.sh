#!/bin/bash

# stop on exit
set -e

# Check Installation supports this example
checkinstall.exe -p install.pkg --nobanner

# Must ensure we re-build with modifications for coverage
make clean

make -C application/google

make compileVerilog TESTBENCH=tb_single COVERAGE=1

make compileOVPmodel

make run TESTBENCH=tb_single COVERAGE=1 \
         PLUSARGS="+elf_file=application/google/riscv_arithmetic_basic_test_0.RISCV32.elf \
                   +nm_file=application/google/riscv_arithmetic_basic_test_0.RISCV32.nm \
                   +ovpcfg=\"--override root/cpu0/_intercept/symbol=_exit --trace --tracechange\" \
                   +disass"

make coverage TESTBENCH=tb_single COVERAGE=1
