# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh
source verif/regress/install-riscv-tests.sh

source ./verif/sim/setup-env.sh

if ! [ -n "$DV_TARGET" ]; then
  # DV_TARGET=cv64a6_imafdc_sv39_hpdcache
  DV_TARGET=cv64a6_imafdc_sv39
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-testharness,spike
fi

if ! [ -n "$DV_TESTLISTS" ]; then
  DV_TESTLISTS="../tests/testlist_riscv-tests-$DV_TARGET-p.yaml \
                ../tests/testlist_riscv-tests-$DV_TARGET-v.yaml"
  # DV_TESTLISTS="../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-v.yaml"
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"

cd verif/sim
for TESTLIST in $DV_TESTLISTS
do
  python3 cva6.py --testlist=$TESTLIST --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml $DV_OPTS
done

make -C ../.. clean
make clean_all

cd -
