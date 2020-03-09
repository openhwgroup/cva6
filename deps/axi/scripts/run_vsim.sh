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
# Andreas Kurth  <akurth@iis.ee.ethz.ch>

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

[ ! -z "$VSIM" ] || VSIM=vsim

call_vsim() {
    echo "run -all" | $VSIM "$@" | tee vsim.log 2>&1
    grep "Errors: 0," vsim.log
}

for DW in 8 16 32 64 128 256 512 1024; do
    call_vsim tb_axi_lite_to_axi -GDW=$DW -t 1ps -c
done

for DW in 8 16 32 64 128 256 512 1024; do
    for (( MULT = 2; MULT <= `echo 1024/$DW`; MULT *= 2 )); do
        call_vsim tb_axi_dw_downsizer -GDW=$DW -GMULT=$MULT -t 1ps -c
    done
done

for DW in 8 16 32 64 128 256 512 1024; do
    for (( MULT = `echo 1024/$DW | bc`; MULT > 1; MULT /= 2 )); do
        call_vsim tb_axi_dw_upsizer -GDW=$DW -GMULT=$MULT -t 1ps -c
    done
done

call_vsim tb_axi_delayer
call_vsim tb_axi_atop_filter -GN_TXNS=1000
call_vsim tb_axi_xbar -t 1ns -coverage -voptargs="+acc +cover=bcesfx"
call_vsim tb_axi_lite_xbar -t 1ns -coverage -voptargs="+acc +cover=bcesfx"
call_vsim tb_axi_cdc
call_vsim tb_axi_lite_to_apb -t 1ns -coverage -voptargs="+acc +cover=bcesfx"
call_vsim tb_axi_lite_mailbox -t 1ns -coverage -voptargs="+acc +cover=bcesfx"
call_vsim tb_axi_to_axi_lite -t 1ns -coverage -voptargs="+acc +cover=bcesfx"
