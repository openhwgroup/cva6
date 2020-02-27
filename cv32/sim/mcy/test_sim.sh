#!/bin/bash

exec 2>&1
set -ex

{
	echo "read_ilang ../../database/design.il"
	while read -r idx mut; do
		echo "mutate ${mut#* }"
	done < input.txt
	echo "write_verilog -attr2comment mutated.sv"
} > mutate.ys

yosys -ql mutate.log mutate.ys

make -f ../../Makefile verilate
make -f ../../Makefile firmware-build
./testbench_verilator +firmware=firmware.hex > sim.out || true
NERR=`grep -c "ERROR" sim.out`

if [[ "$NERR" -eq 2 ]]
then
  echo "1 PASS" > output.txt
else
  echo "1 FAIL" > output.txt
fi

# if ./testbench_verilator +firmware=firmware.hex > sim.out
# then
# echo "1 TODO" > output.txt
# else
# echo "1 ERROR" > output.txt
# fi
