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

[ ! -z "$SYNOPSYS_DC" ] || SYNOPSYS_DC="synopsys dc_shell -64"

echo 'remove_design -all' > ./synth.tcl
bender synopsys -t synth_test >> ./synth.tcl
echo 'elaborate synth_bench' >> ./synth.tcl

cat ./synth.tcl | $SYNOPSYS_DC | tee synth.log 2>&1
grep -i 'warning:' synth.log || true
! grep -i 'error:' synth.log
