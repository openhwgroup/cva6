#!/bin/bash
# Copyright 2025 Isaar AHMAD
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Isaar AHMAD
#
# ==============================================================================
# This script demonstrates how to simulate the CVA6 core using Verilator and the 
# RISC-V Proxy Kernel (PK), using the DV_SIMULATOR "veri-testharness-pk".
# It runs two hello world simulations, one for a  64-bit target, and one for a 
# 32-bit target. Both simulations are run in separate subshell(s) to isolate 
# environment changes and directory moves.
#
# Usage (from the base of the repository):
#   bash verif/regress/veri-testharness-pk-tests.sh
#
# ==============================================================================
# Exit immediately if a command exits with a non-zero status.
set -e

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: The RISCV environment variable is not defined."
  return
fi

# Set the NUM_JOBS variable to increase the number of parallel make jobs
# export NUM_JOBS=

# Global simulation settings, common to all runs.
export DV_SIMULATORS="veri-testharness-pk"
TIMEOUT_WALLCLOCK="800"
TIMEOUT_TICKS="5000000"

# ==============================================================================
# Core simulation function
# This function wraps the entire process for running a single CVA6
# simulation. It is parameterized to handle different target configurations.
#
# Args:
#  $1: Target architecture (DV_TARGET)
#  $2: Proxy kernel architecture (PK_ARCH)
#  $3: Proxy kernel ABI (PK_MABI)
# ==============================================================================
run_cva6_simulation() {
  # Use local variables to avoid polluting the global scope.
  local DV_TARGET=$1
  local PK_ARCH=$2
  local PK_MABI=$3

  # Run the logic in a subshell to isolate environment changes.
  (
    # Exit this subshell immediately if a command fails.
    set -e

    # Export the configuration specific to this simulation run.
    export DV_TARGET
    export PK_ARCH
    export PK_MABI

    echo "--------------------------------------------------------"
    echo "[ CVA6 ] Target:        ${DV_TARGET}"
    echo "[ CVA6 ] PK Arch:       ${PK_ARCH}"
    echo "[ CVA6 ] PK MABI:       ${PK_MABI}"
    echo "--------------------------------------------------------"

    # Install verilator if required by the simulator choice.
    if [[ "$DV_SIMULATORS" == *"veri-testharness"* ]]; then
      source ./verif/regress/install-verilator.sh
    fi

    # Install RISC-V Proxy Kernel for the specified architecture.
    # The log file is named after the target to prevent overwrites.
    if [[ "$DV_SIMULATORS" == *"veri-testharness-pk"* ]]; then
      local pk_log_file="./verif/sim/pk-install-${DV_TARGET}.log"
      echo "[ riscv-pk ] Installing RISC-V proxy kernel for ${DV_TARGET}..."
      source ./verif/regress/install-pk.sh ${PK_ARCH} ${PK_MABI} > ${pk_log_file} 2>&1
      echo "[ riscv-pk ] Installation logs available at: $(pwd)/${pk_log_file}"
      echo "[ riscv-pk ] PK_INSTALL_DIR is ${PK_INSTALL_DIR}"
    fi

    # Set up the simulation environment. navigate to simulation directory.
    source ./verif/sim/setup-env.sh
    cd ./verif/sim

    # GCC options (customize if needed).
    local CC_OPTS=""

    echo "[ CVA6 ] Starting pytohn simulation script..."
    # Execute the main simulation command.
    python3 cva6.py \
	    --target "$DV_TARGET" \
	    --iss="$DV_SIMULATORS" \
	    --iss_yaml=cva6.yaml \
	    --iss_timeout="$TIMEOUT_WALLCLOCK" \
	    --c_tests ../tests/custom/hello_world/hello_world.c \
	    --gcc_opts="$CC_OPTS" \
	    --issrun_opts="+time_out=$TIMEOUT_TICKS"
  )
}

# ==============================================================================
# Main Execution
# This block calls run_simulation_cva6 twice - once for each simulation run.
# ==============================================================================
export DV_TARGET1="cv64a6_imafdc_sv39"
export PK_ARCH1="rv64gc_zba_zbb_zbs_zbc_zbkb_zbkx_zkne_zknd_zknh"
export PK_MABI1="lp64d"

export DV_TARGET2="cv32a6_imac_sv32"
export PK_ARCH2="rv32imac_zbkb_zbkx_zkne_zknd_zknh_zicsr_zifencei"
export PK_MABI2="ilp32"

COLOR_GREEN='\033[0;32m'
COLOR_NONE='\033[0m' # No Color
# --- Simulation 1: cv64a6_imafdc_sv39
echo -e "${COLOR_GREEN} ============== Starting simualtion 1: ${DV_TARGET1} ====================== ${COLOR_NONE}"
run_cva6_simulation ${DV_TARGET1} ${PK_ARCH1} ${PK_MABI1}
echo -e "${COLOR_GREEN} ============== Finished simulation 1: ${DV_TARGET1} ====================== ${COLOR_NONE}"

# --- Simulation 2: cv32a6_imac_sv32 ---
echo -e "${COLOR_GREEN} ============== Starting simualtion 2: ${DV_TARGET2} ====================== ${COLOR_NONE}"
run_cva6_simulation ${DV_TARGET2} ${PK_ARCH2} ${PK_MABI2}
echo -e "${COLOR_GREEN} ============== Finished simulation 2: ${DV_TARGET2} ====================== ${COLOR_NONE}"

echo "All simulations finished successfully."
