# Copyright 2026 PlanV Technologies
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Angela Gonzalez - PlanV

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-testharness,spike
fi

# install the required tools
if [[ "$DV_SIMULATORS" == *"veri-testharness"* ]]; then
  source ./verif/regress/install-verilator.sh
fi
source ./verif/regress/install-spike.sh

# setup sim env
source ./verif/sim/setup-env.sh

echo "$SPIKE_INSTALL_DIR$"

if ! [ -n "$UVM_VERBOSITY" ]; then
    export UVM_VERBOSITY=UVM_NONE
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"

cd verif/sim/
make clean_all

python3 cva6.py --target cv32a65x_noPMP --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_tests ../tests/custom/zcmt/cm_jalt_long_ret.S --linker=../tests/custom/zcmt/link.ld --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib"
python3 cva6.py --target cv32a65x_noPMP --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_tests ../tests/custom/zcmt/cm_jalt_long.S --linker=../tests/custom/zcmt/link.ld --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib"
python3 cva6.py --target cv32a65x_noPMP --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_tests ../tests/custom/zcmt/cm_jt_long.S --linker=../tests/custom/zcmt/link.ld --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib"
python3 cva6.py --target cv32a65x_noPMP --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --asm_tests ../tests/custom/zcmt/jvt_csr.S --linker=../tests/custom/zcmt/link.ld --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib"

make clean_all
cd -
