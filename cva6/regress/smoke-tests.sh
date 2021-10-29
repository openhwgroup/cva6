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
  DV_SIMULATORS=veri-core,spike
fi

cd cva6/sim/
python3 cva6.py --testlist=../tests/testlist_riscv-tests-rv64gc-v.yaml --test rv64ui-v-add --iss_yaml cva6.yaml --target rv64gc --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-tests-rv64gc-p.yaml --test rv64ui-p-add --iss_yaml cva6.yaml --target rv64gc --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-compliance-rv64gc.yaml --test rv32i-I-ADD-01 --iss_yaml cva6.yaml --target rv64gc --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --target rv64gc --iss=veri-core,spike --iss_yaml=cva6.yaml --c_tests ../tests/custom/hello_word/hello_word.c --gcc_opts "-g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -T ../tests/custom/common/test.ld"
make -C ../../core-v-cores/cva6 clean
python3 cva6.py --testlist=../tests/testlist_riscv-compliance-rv32ima.yaml --test rv32i-I-ADD-01 --iss_yaml cva6.yaml --target rv32imac --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-tests-rv32ima-p.yaml --test rv32ui-p-add --iss_yaml cva6.yaml --target rv32imac --iss=$DV_SIMULATORS $DV_OPTS
cd -
