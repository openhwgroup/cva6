# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./cva6/regress/install-cva6.sh
source ./cva6/regress/install-riscv-dv.sh
source ./cva6/regress/install-riscv-compliance.sh
source ./cva6/regress/install-riscv-tests.sh

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-uvm,spike
fi

cd cva6/sim/riscv-dv
python3 run.py --testlist=../../tests/testlist_riscv-tests-rv64gc-v.yaml --test rv64ui-v-add --target rv64gc --iss=$DV_SIMULATORS $DV_OPTS
python3 run.py --testlist=../../tests/testlist_riscv-tests-rv64gc-p.yaml --test rv64ui-p-add --target rv64gc --iss=$DV_SIMULATORS $DV_OPTS
python3 run.py --testlist=../../tests/testlist_riscv-compliance-rv64gc.yaml --test rv32i-I-ADD-01 --target rv64gc --iss=$DV_SIMULATORS $DV_OPTS
make -C ../../../core-v-cores/cva6 clean
python3 run.py --testlist=../../tests/testlist_riscv-compliance-rv32ima.yaml --test rv32i-I-ADD-01 --target rv32imac --iss=$DV_SIMULATORS $DV_OPTS
python3 run.py --testlist=../../tests/testlist_riscv-tests-rv32ima-p.yaml --test rv32ui-p-add --target rv32imac --iss=$DV_SIMULATORS $DV_OPTS
cd ../../..
