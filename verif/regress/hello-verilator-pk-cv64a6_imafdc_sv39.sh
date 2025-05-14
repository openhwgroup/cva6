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
TIMEOUT_TICKS="5000000"
export DV_SIMULATORS="veri-testharness-pk"
export DV_TARGET="cv64a6_imafdc_sv39"
export PK_ARCH="rv64gc_zba_zbb_zbs_zbc_zbkb_zbkx_zkne_zknd_zknh"
export PK_MABI="lp64d"

if [[ "$DV_SIMULATORS" == *"veri-testharness"* ]]; then
  source ./verif/regress/install-verilator.sh
fi

if [[ "$DV_SIMULATORS" == *"veri-testharness-pk"* ]]; then

  echo "[ riscv-pk ] veri-testharness-pk simulation detected. Installing RISC-V proxy kernel..."
  source ./verif/regress/install-pk.sh ${PK_ARCH} ${PK_MABI} > ./verif/sim/pk-install.log 2>&1
  echo "[ riscv-pk ] RISC-V proxy kernel installation logs at $(pwd)/verif/sim/pk-install.log"
  echo "[ riscv-pk ] PK_INSTALL_DIR is ${PK_INSTALL_DIR}"
fi

source ./verif/sim/setup-env.sh
cd ./verif/sim

CC_OPTS=""

python3 cva6.py --target $DV_TARGET --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --iss_timeout=$TIMEOUT_WALLCLOCK \
--c_tests ../tests/custom/hello_world/hello_world.c \
--gcc_opts="$CC_OPTS" \
--issrun_opts="+time_out=$TIMEOUT_TICKS"
