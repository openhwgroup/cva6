#!/bin/bash

#
# Compliance Test Application Source and ELF
#   The compliance test application source and ELF files are 
#   taken directly from the compliance test suite and they
#   are not compiled locally
#

# stop on exit
set -e

# Check Installation supports this example
checkinstall.exe -p install.pkg --nobanner

make compileVerilog TESTBENCH=tb_single \
                    PLUSDEFS="+define+T0_TYPE=\\\"RV32IM\\\""

make compileOVPmodel

mkdir -p $(pwd)/out/compliance

make run TESTBENCH=tb_single \
         PLUSARGS="+elf_file=application/compliance/MUL.RV32IM.elf \
                   +nm_file=application/compliance/MUL.RV32IM.nm \
                   +stdout_file=$(pwd)/out/compliance/MUL  \
                   +sig_file=$(pwd)/out/compliance/MUL"

echo "# Check Signature"
# Compare the generated signature against a saved reference
sdiff application/compliance/MUL.RV32IM.signature $(pwd)/out/compliance/MUL.RV32IM.0.sig > $(pwd)/out/compliance/MUL.RV32IM.0.sig.sdiff
if [ $? -eq 0 ]; then
  echo "# PASS - Signatures match"
else
  echo "# FAIL"
fi
