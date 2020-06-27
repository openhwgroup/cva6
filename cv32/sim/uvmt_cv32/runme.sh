#!/bin/bash
# Shell commands to compile assembler source for the CV32E40P testbench
# using the CV32E40P Board Support Package. 
# Assumes you are in $<wrk_cv32e40p>/cv32/sim/uvmt_cv32.
# Also generates a HEX file for verilog, a readelf and objdump,
# and greps out the Entry point address from the readelf (s.b. 0x80).

function assemble_me() {
  make clean-bsp
  make bsp

  /opt/riscv/bin/riscv32-unknown-elf-gcc -Os -g -static -mabi=ilp32 -march=rv32imc -Wall -pedantic \
	  -o ../../tests/core/$1/$2.elf \
	  -nostartfiles \
	  -I ../../tests/core/$1 \
	  ../../tests/core/$1/$2.S \
	  -T ../../bsp/link.ld \
	  -L ../../bsp \
	  -lcv-verif

  /opt/riscv/bin/riscv32-unknown-elf-objcopy \
	  -O verilog \
	  ../../tests/core/$1/$2.elf \
	  ../../tests/core/$1/$2.hex

  /opt/riscv/bin/riscv32-unknown-elf-readelf \
	  -a \
	  ../../tests/core/$1/$2.elf > \
	  ../../tests/core/$1/$2.readelf

  /opt/riscv/bin/riscv32-unknown-elf-objdump \
	  -D \
	  ../../tests/core/$1/$2.elf > \
	  ../../tests/core/$1/$2.objdump
}

make clean_core_tests
ls -l ../../tests/core/custom
assemble_me custom riscv_ebreak_test_0
assemble_me custom riscv_arithmetic_basic_test_0
ls -l ../../tests/core/custom
grep -i entry ../../tests/core/custom/*.readelf
echo ""
echo ""
ls -l ../../tests/core/google-riscv-dv
assemble_me google-riscv-dv riscv_arithmetic_basic_test_0
assemble_me google-riscv-dv riscv_arithmetic_basic_test_1
ls -l ../../tests/core/google-riscv-dv
grep -i entry ../../tests/core/google-riscv-dv/*.readelf

#end#end#

# $ make corev-dv 
# $ make custom CUSTOM_DIR=/data/mike/GitHubRepos/openhwgroup/core-v-verif/isg_tests/cv32/tests/core/google-riscv-dv CUSTOM_PROG=corev_asm_test_0
# $ make custom CUSTOM_DIR=/data/mike/GitHubRepos/openhwgroup/core-v-verif/isg_tests/cv32/tests/core/google-riscv-dv CUSTOM_PROG=corev_asm_test_1
