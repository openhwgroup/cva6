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

FW_DIR=$PWD/../../../../../cv32/tests/core/firmware
MAKEFLAGS="CV32E40P_MANIFEST=$PWD/../../cv32e40p_manifest.flist PROJ_ROOT_DIR=$PWD/../../../../.."
MAKEFILE=../../Makefile
make -f $MAKEFILE $MAKEFLAGS verilate
make -f $MAKEFILE $MAKEFLAGS $FW_DIR/firmware.hex
cp $FW_DIR/firmware.hex firmware.hex
timeout 1m ./testbench_verilator +firmware=firmware.hex > sim.out || true

if [[ `grep -c "ERROR" sim.out` -eq 2 ]]
then
  echo "1 PASS" > output.txt
else
  echo "1 FAIL" > output.txt
fi

return 0
# if ./testbench_verilator +firmware=firmware.hex > sim.out
# then
# echo "1 TODO" > output.txt
# else
# echo "1 ERROR" > output.txt
# fi
