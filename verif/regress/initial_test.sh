#!/bin/bash

# setup sim env
source ./verif/sim/setup-env.sh
# setup simulators
export DV_SIMULATORS=veri-testharness,spike

# set the target
DV_TARGET = cv64a6_imafdc_sv39

if ! [ -n "$UVM_VERBOSITY" ]; then
  export UVM_VERBOSITY=UVM_NONE
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"

cd verif/sim/

python3 cva6.py --target ${DV_TARGET} --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/hello_world/hello_world.c \
  --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -T ../tests/custom/common/test.ld" $DV_OPTS

cd ../..
