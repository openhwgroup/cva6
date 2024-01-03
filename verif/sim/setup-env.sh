# CVA6 project root
export ROOT_PROJECT=$(readlink -f $(dirname "${BASH_SOURCE[0]}")/../..)

export RTL_PATH=$ROOT_PROJECT/
export TB_PATH=$ROOT_PROJECT/verif/tb/core
export TESTS_PATH=$ROOT_PROJECT/verif/tests

if [ -z "$RISCV" ]; then
  echo "Error: RISCV variable undefined."
  return
fi
# Set RISCV toolchain-related variables
export LIBRARY_PATH="$RISCV/lib"
export LD_LIBRARY_PATH="$RISCV/lib:$LD_LIBRARY_PATH"
export C_INCLUDE_PATH="$RISCV/include"
export CPLUS_INCLUDE_PATH="$RISCV/include"

# Auto-detect RISC-V tool name prefix if not explicitly given.
if [ -z "$CV_SW_PREFIX" ]; then
    export CV_SW_PREFIX="$(ls -1 -r $RISCV/bin/riscv*-gcc | head -n 1| grep gcc | rev | cut -d '/' -f 1 | cut -d '-' -f 2- | rev)-"
fi
# Default to auto-detected GCC name if not explicitly given.
if [ -z "$RISCV_GCC" ]; then
    export RISCV_GCC=$RISCV/bin/${CV_SW_PREFIX}gcc
fi
# Default to auto-detected OBJCOPY name if not explicitly given.
if [ -z "$RISCV_OBJCOPY" ]; then
    export RISCV_OBJCOPY=$RISCV/bin/${CV_SW_PREFIX}objcopy
fi

# Set verilator and spike related variables
if [ -z "$VERILATOR_INSTALL_DIR" ]; then
    export VERILATOR_INSTALL_DIR="$ROOT_PROJECT"/tools/$(ls $ROOT_PROJECT/tools | grep verilator)
fi

if [ -z "$SPIKE_SRC_DIR" -o "$SPIKE_INSTALL_DIR" = "__local__" ]; then
  export SPIKE_SRC_DIR=$ROOT_PROJECT/verif/core-v-verif/vendor/riscv/riscv-isa-sim
fi

if [ -z "$SPIKE_INSTALL_DIR" -o "$SPIKE_INSTALL_DIR" = "__local__" ]; then
    export SPIKE_INSTALL_DIR="$ROOT_PROJECT"/tools/spike
fi

export SPIKE_PATH=$SPIKE_INSTALL_DIR/bin

# Update the PATH to add all the tools
export PATH="$VERILATOR_INSTALL_DIR/bin:$RISCV/bin:$PATH"
