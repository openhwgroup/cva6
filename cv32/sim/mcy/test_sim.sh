#!/bin/bash

exec 2>&1
set -ex

{
	echo "read_ilang ../../database/design.il"
	while read -r idx mut; do
		echo "mutate -ctrl mutsel 8 ${idx} ${mut#* }"
	done < input.txt
	echo "opt_rmdff"
	echo "rename riscv_alu_div mutated"
	echo "write_verilog -attr2comment mutated.sv"
} > mutate.ys

yosys -ql mutate.log mutate.ys

TEST_DIR=$PWD/../../../../../cv32/tests/core/
MAKEFLAGS="CV32E40P_MANIFEST=$PWD/../../cv32e40p_manifest.flist PROJ_ROOT_DIR=$PWD/../../../../.."
MAKEFILE=../../Makefile
make -f $MAKEFILE $MAKEFLAGS testbench_verilator_mut

while read idx mut; do
	# shorter firmware first
	make -f $MAKEFILE $MAKEFLAGS $TEST_DIR/div_only_firmware/div_only_firmware.hex
	cp $TEST_DIR/div_only_firmware/div_only_firmware.hex div_only_firmware.hex
	if ! timeout 1m ./testbench_verilator +firmware=div_only_firmware.hex --mutidx ${idx} > sim_short_${idx}.out || ! grep "PASSED" sim_short_${idx}.out
	then
		echo "${idx} FAIL" >> output.txt
		continue
	fi

	# longer firmware if short doesn't catch anything
	make -f $MAKEFILE $MAKEFLAGS $TEST_DIR/firmware/firmware.hex
	cp $TEST_DIR/firmware/firmware.hex firmware.hex
	timeout 1m ./testbench_verilator +firmware=firmware.hex --mutidx ${idx} > sim_long_${idx}.out || true

	if [[ `grep -c "ERROR" sim_long_${idx}.out` -ne 2 ]]
	then
		echo "${idx} FAIL" >> output.txt
		continue
	fi

	echo "$idx PASS" >> output.txt
done < input.txt
