# Copyright 2023 Thales DIS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI - Thales

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh

source ./verif/sim/setup-env.sh


export cov=1 #enable the Code Coverage

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv32a65x
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-uvm,spike
fi

cd verif/sim/
python3 cva6.py --testlist=../tests/testlist_csr_embedded.yaml --iss_yaml cva6.yaml --target $DV_TARGET --iss=$DV_SIMULATORS $DV_OPTS --priv=m -i 1

cd -
