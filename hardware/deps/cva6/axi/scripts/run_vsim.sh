#!/bin/bash
# Copyright (c) 2014-2018 ETH Zurich, University of Bologna
#
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$VSIM" ] || VSIM=vsim

call_vsim() {
	echo "run -all" | $VSIM "$@" | tee vsim.log 2>&1
	grep "Errors: 0," vsim.log
}

for DW in 8 16 32 64 128 256 512 1024; do
	call_vsim tb_axi_lite_to_axi -GDW=$DW -t 1ps -c
	call_vsim tb_axi_to_axi_lite -GDW=$DW -t 1ps -c
done

test_axi_lite_xbar() {
	call_vsim tb_axi_lite_xbar -GNUM_MASTER=$1 -GNUM_SLAVE=$2 -t 1ps -c
}

# regression test cases
test_axi_lite_xbar 1 1
# test_axi_lite_xbar 4 9 # This seems to be a bug in ModelSim!

for NM in 1 2 3 4 8; do
	test_axi_lite_xbar $NM 4
done

for NS in 1 2 3 4 8; do
	test_axi_lite_xbar 4 $NS
done

call_vsim tb_axi_delayer
call_vsim tb_axi_id_remap
call_vsim tb_axi_atop_filter -GN_TXNS=1000
