# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the License);
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon


# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi


# install the required tools
source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh

# install the required test suites
source ./verif/regress/install-riscv-tests.sh

# setup sim env
source ./verif/sim/setup-env.sh

echo "$SPIKE_INSTALL_DIR$"

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-testharness,spike
fi

if ! [ -n "$UVM_VERBOSITY" ]; then
    export UVM_VERBOSITY=UVM_NONE
fi

export cvxif=1 # For CVXIF in Spike
export DV_OPTS="$DV_OPTS --issrun_opts=+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"


cd verif/sim/
make -C ../.. clean
make clean_all
python3 cva6.py --testlist=../tests/testlist_cvxif.yaml --test cvxif_add_nop --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
make -C ../.. clean
make clean_all
python3 cva6.py --testlist=../tests/testlist_cvxif.yaml --test cvxif_add_nop --iss_yaml cva6.yaml --target cv32a65x --iss=$DV_SIMULATORS $DV_OPTS
make -C ../.. clean
make clean_all

cd -
