# Make sure to source this script from the root directory 
# to correctly set the environment variables related to the tools

# Set the NUM_JOBS variable to increase the number of parallel make jobs
# export NUM_JOBS=
# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

TIMEOUT_WALLCLOCK="600"
TIMEOUT_TICKS="2100000"
#export TRACE_COMPACT=1
export DV_SIMULATORS="veri-testharness-pk"
export DV_TARGET="cv64a6_imafdc_sv39"

if [[ "$DV_SIMULATORS" == *"veri-testharness"* ]]; then
  source ./verif/regress/install-verilator.sh
fi

source ./verif/sim/setup-env.sh
cd ./verif/sim

# CC_OPTS="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -lgcc"
CC_OPTS=""

python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --iss_timeout=$TIMEOUT_WALLCLOCK \
--c_tests ../tests/custom/hello_world/hello_world.c \
--gcc_opts="$CC_OPTS" \
--issrun_opts="+time_out=$TIMEOUT_TICKS"
