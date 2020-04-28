#!/bin/bash

# stop on exit
set -e

# Check Installation supports this example
checkinstall.exe -p install.pkg --nobanner

make -C application/C_applications APP=dhrystone

make compileVerilog TESTBENCH=tb_single

make compileOVPmodel

make run TESTBENCH=tb_single \
         PLUSARGS="+elf_file=application/C_applications/dhrystone.RISCV32.elf \
                   +nm_file=application/C_applications/dhrystone.RISCV32.nm"

