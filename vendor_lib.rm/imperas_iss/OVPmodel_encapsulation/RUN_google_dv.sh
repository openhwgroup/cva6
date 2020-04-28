#!/bin/bash

# stop on exit
set -e

# Check Installation supports this example
checkinstall.exe -p install.pkg --nobanner

make -C application/google

make compileVerilog TESTBENCH=tb_single

make compileOVPmodel

make run TESTBENCH=tb_single \
         PLUSARGS="+elf_file=application/google/riscv_arithmetic_basic_test_0.RISCV32.elf \
                   +nm_file=application/google/riscv_arithmetic_basic_test_0.RISCV32.nm \
                   +ovpcfg=\"--override root/cpu0/_intercept/symbol=_exit --trace --tracechange\""
