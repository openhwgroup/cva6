# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume CHAUVON (guillaume.chauvon@thalesgroup.fr)

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./cva6/regress/install-cva6.sh
source ./cva6/regress/install-riscv-dv.sh
source ./cva6/regress/install-riscv-compliance.sh

if ! [ -n "$DV_SIMULATORS" ]; then
  echo "Error DV_SIMULATORS variable undefined"
fi
if ! [ -n "$DV_TARGET" ]; then
  echo "Error DV_TARGET variable undefined"
fi

cd cva6/sim/
python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --testlist=../tests/testlist_riscv-compliance-$DV_TARGET.yaml --test rv32ui-addi
make -C ../../core-v-cores/cva6 clean
make clean_all

cd -
