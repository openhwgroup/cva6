# Copyright 2022 Thales DIS France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Zbigniew CHAMSKI (zbigniew.chamski@thalesgroup.fr)

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
  DV_SIMULATORS=veri-testharness,spike
fi

cd cva6/sim/
python3 cva6.py --testlist=../tests/testlist_issues.yaml --test compressed-fpreg-commits-rv64 --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
make -C ../../core-v-cores/cva6 clean
make clean_all
python3 cva6.py --testlist=../tests/testlist_issues.yaml --test compressed-fpreg-commits-rv32 --iss_yaml cva6.yaml --target cv32a6_imafc_sv32 --iss=$DV_SIMULATORS $DV_OPTS
make -C ../../core-v-cores/cva6 clean
make clean_all

cd -
