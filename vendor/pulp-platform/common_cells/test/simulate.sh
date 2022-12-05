#!/usr/bin/env bash
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

set -e

[ ! -z "$VSIM" ] || VSIM=vsim

bender script vsim -t test > compile.tcl

"$VSIM" -c -quiet -do 'source compile.tcl; quit'

call_vsim() {
	echo "run -all" | "$VSIM" "$@" | tee vsim.log 2>&1
	grep "Errors: 0," vsim.log
}

#call_vsim cdc_fifo_tb # currently broken
for tb in cdc_2phase_tb fifo_tb graycode_tb id_queue_tb popcount_tb stream_register_tb addr_decode_tb; do
    call_vsim $tb
done

for depth in 0 1 2; do
	call_vsim stream_to_mem_tb -gBufDepth=$depth -coverage -voptargs="+acc +cover=bcesfx"
done

for num in 1 4 7; do
  call_vsim rr_arb_tree_tb -GNumInp=$num -coverage -voptargs="+acc +cover=bcesfx" -suppress vsim-3009
done

for spill_reg in 0 1; do
  for num_inp in 1 4 18; do
    for num_out in 1 4 18; do
      call_vsim stream_xbar_tb -gNumInp=$num_inp -gNumOut=$num_out -gSpillReg=$spill_reg -coverage -voptargs="+acc +cover=bcesfx"
    done
  done
done

for radix in 2 4 8; do
  for num_inp in 1 2 17 64; do
    for num_out in 1 2 4 16 17 64; do
      call_vsim stream_omega_net_tb -gDutNumInp=$num_inp -gDutNumOut=$num_out -gDutRadix=$radix -coverage -voptargs="+acc +cover=bcesfx"
    done
  done
done

for dut in "spill_register" "4phase_handshake"; do
  for clk in 1,1 1,2 2,1 1,4 5,1 3,6 8,4; do
    IFS=',' read src_clk dst_clk <<< "${clk}"
    call_vsim isochronous_crossing_tb -gDUT=$dut -gTCK_SRC_MULT=$src_clk -gTCK_DST_MULT=$dst_clk
  done
done
