###############################################################################
#
# Copyright 2020 Thales DIS Design Services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
###############################################################################
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@invia.fr)
#
###############################################################################

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./cva6/install-cva6.sh
source ./cva6/install-riscv-dv.sh
source ./cva6/install-riscv-compliance.sh
source ./cva6/install-riscv-tests.sh

cd uvm/riscv-dv
python3 run.py --testlist=../../cva6/tests/testlist_riscv-tests-rv64gc-v.yaml --test rv64ui-v-add --target rv64gc --iss=verilator,spike $DV_OPTS
python3 run.py --testlist=../../cva6/tests/testlist_riscv-tests-rv64gc-p.yaml --test rv64ui-p-add --target rv64gc --iss=verilator,spike $DV_OPTS
python3 run.py --testlist=../../cva6/tests/testlist_riscv-compliance-rv64gc.yaml --test rv32i-I-ADD-01 --target rv64gc --iss=verilator,spike $DV_OPTS
cd ../../core-v-cores/cva6/; git apply ../../cva6/cva6-32bit.patch; cd -
python3 run.py --testlist=../../cva6/tests/testlist_riscv-compliance-rv32ima.yaml --test rv32i-I-ADD-01 --target rv32imac --iss=verilator,spike $DV_OPTS
python3 run.py --testlist=../../cva6/tests/testlist_riscv-tests-rv32ima-p.yaml --test rv32ui-p-add --target rv32imac --iss=verilator,spike $DV_OPTS
cd ../../core-v-cores/cva6/; git apply --reverse ../../cva6/cva6-32bit.patch; cd -
cd ../..
