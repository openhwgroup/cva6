# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon (guillaume.chauvon@thalesgroup.com)

# where are the tools
if ! [ -n "$RISCV_PREFIX" ]; then
  echo "Error: RISCV_PREFIX variable undefined"
  return
fi

# install the required tools
source ./cva6/regress/install-cva6.sh
source ./cva6/regress/install-riscv-dv.sh

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-testharness,spike
fi


cd cva6/tests/riscv-tests/benchmarks

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv64a6_imafdc_sv39
fi

make clean
make

for f in *.riscv; do
    mv -- "$f" "${f%.riscv}.o"
done

cd -
cd cva6/sim/

python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/dhrystone.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/median.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/mm.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/mt-matmul.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/mt-vvadd.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/multiply.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/pmp.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/qsort.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/rsort.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/spmv.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/towers.o
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml cva6.yaml --elf_tests ../tests/riscv-tests/benchmarks/vvadd.o

make -C ../../core-v-cores/cva6 clean
make clean_all
cd -

cd cva6/tests/riscv-tests/benchmarks
for f in *.o; do
    mv -- "$f" "${f%.o}.riscv"
done
cd -
