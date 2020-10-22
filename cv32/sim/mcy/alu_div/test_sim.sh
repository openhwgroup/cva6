#!/bin/bash

#
# Copyright 2020 OpenHW Group
# Copyright 2020 Symbiotic EDA
#
# Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#

exec 2>&1
set -ex

# create yosys script for exporting mutation
{
	echo "read_ilang ../../database/design.il"
	while read -r idx mut; do
		# add multiple mutations to module, selectable with 'mutsel' input
		echo "mutate -ctrl mutsel 8 ${idx} ${mut#* }"
	done < input.txt
	echo "opt_rmdff" # workaround for verilator not supporting posedge 1'b1
	echo "rename riscv_alu_div mutated"
	echo "write_verilog -attr2comment mutated.sv"
} > mutate.ys

# export mutated.sv
yosys -ql mutate.log mutate.ys

# locations
PROJ_ROOT_DIR=$PWD/../../../../../..
TEST_DIR=$PROJ_ROOT_DIR/cv32/tests/core

# create modified manifest
grep -v "riscv_alu_div.sv" $PROJ_ROOT_DIR/core-v-cores/cv32e40p/cv32e40p_manifest.flist > mutated_manifest.flist
echo "../../riscv_alu_div_mutated_wrapper.sv" >> mutated_manifest.flist
echo "mutated.sv" >> mutated_manifest.flist

# build verilator testbench with mutated module
MAKEFLAGS="CV32E40P_MANIFEST=mutated_manifest.flist PROJ_ROOT_DIR=$PROJ_ROOT_DIR"
MAKEFILE=../../Makefile
make -f $MAKEFILE $MAKEFLAGS testbench_verilator

# for each mutation (listed in input.txt)
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
