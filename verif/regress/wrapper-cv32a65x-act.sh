#!/bin/bash
# Run ACT 4.0 tests on cv32a65x via Makefile targets

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

set -e

# ================== CONFIGURATION ==================
export CVA6_REPO_DIR="${HOME}/cva6"
export ACT4_PKG="${HOME}/cva6/external/act4"
export TARGET_RTL="cv32a65x"

# Toolchain configuration
export RISCV="${HOME}/riscv_toolchain"
export PATH="${RISCV}/bin:${PATH}"
export CV_SW_PREFIX="riscv64-unknown-elf-"
export max_cycles=2000000

echo "Environment Setup Complete"
cd "${CVA6_REPO_DIR}"

# Build the Verilator model
echo "Building Verilator model for ${TARGET_RTL}"
make verilate target=${TARGET_RTL} -j$(nproc)

cd "${CVA6_REPO_DIR}/verif/sim"

# Run generation and certification via Makefile
# This triggers the 'gen' then 'certify' targets defined in verif/sim/Makefile
echo "Starting ACT Regression (Generation + RTL Simulation)"
make gen-certify target=${TARGET_RTL}

#Display Summary
# Path derived from SIM_RESULTS and VERI_LOG_DIR in Makefile
SUMMARY_FILE="${CVA6_REPO_DIR}/verif/sim/simulation_results/certification_summary.txt"

if [ -f "${SUMMARY_FILE}" ]; then
    echo ""
    cat "${SUMMARY_FILE}"
else
    echo "Error: Summary file not found at ${SUMMARY_FILE}"
    exit 1
fi
