# CVA6 project root
if [ -n "$BASH_VERSION" ]; then
  SCRIPT_PATH="$BASH_SOURCE[0]"
elif [ -n "$ZSH_VERSION" ]; then
  SCRIPT_PATH="${(%):-%N}"
else
  echo "Error: Non recognized shell."
  return
fi
export ROOT_PROJECT=$(readlink -f $(dirname "${SCRIPT_PATH}")/../..)

export RTL_PATH="$ROOT_PROJECT/"
export TB_PATH="$ROOT_PROJECT/verif/tb/core"
export TESTS_PATH="$ROOT_PROJECT/verif/tests"

# RISCV-DV & COREV-DV
export RISCV_DV_ROOT="$ROOT_PROJECT/verif/sim/dv"
export CVA6_DV_ROOT="$ROOT_PROJECT/verif/env/corev-dv"

# Set RISCV toolchain-related variables
export RISCV="$ROOT_PROJECT/util/riscv_toolchain"
export LIBRARY_PATH="$RISCV/lib"
export LD_LIBRARY_PATH="$RISCV/lib:$LD_LIBRARY_PATH"
export C_INCLUDE_PATH="$RISCV/include"
export CPLUS_INCLUDE_PATH="$RISCV/include"

# Auto-detect RISC-V tool name prefix if not explicitly given.
export CV_SW_PREFIX="$(ls -1 $RISCV/bin/riscv* | head -n 1 | rev | cut -d '/' -f 1 | cut -d '-' -f 2- | rev)-"

# Default to auto-detected CC name if not explicitly given.
export RISCV_CC="$RISCV/bin/${CV_SW_PREFIX}gcc"

# Default to auto-detected OBJCOPY name if not explicitly given.
export RISCV_OBJCOPY="$RISCV/bin/${CV_SW_PREFIX}objcopy"


# Set verilator and spike related variables
export VERILATOR_INSTALL_DIR="$ROOT_PROJECT"/tools/verilator-v5.008
export SPIKE_SRC_DIR="$ROOT_PROJECT"/verif/core-v-verif/vendor/riscv/riscv-isa-sim
export SPIKE_INSTALL_DIR="$ROOT_PROJECT"/tools/spike
export SPIKE_PATH="$SPIKE_INSTALL_DIR"/bin

# Update the PATH to add all the tools
export PATH="$VERILATOR_INSTALL_DIR/bin:$RISCV/bin:$PATH"
