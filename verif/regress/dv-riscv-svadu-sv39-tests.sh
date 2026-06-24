# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Seongwon Jo (seongwon.jo@kaist.ac.kr)

if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh
source ./verif/sim/setup-env.sh

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv64a6_imafdc_sv39_hpdcache
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-testharness,spike
fi


cd verif/sim
python3 cva6.py --testlist=../tests/testlist_riscv-svadu-sv39-$DV_TARGET.yaml --target $DV_TARGET --iss_yaml=cva6.yaml --iss=$DV_SIMULATORS $DV_OPTS --spike_extension=svadu
cd -