# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

# Customise this to a fast local disk
export ROOT_PROJECT=$(readlink -f $(dirname "${BASH_SOURCE[0]}")/../../)
export TOP="$ROOT_PROJECT/tools"

# where to install the tools
if [ -z "$RISCV" ]; then
  echo "Error: RISCV variable undefined."
  return
fi

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

# Set up tool-related variables.
export PATH="$RISCV/bin:$PATH"
export LIBRARY_PATH="$RISCV/lib"
export LD_LIBRARY_PATH="$RISCV/lib:$LD_LIBRARY_PATH"
export C_INCLUDE_PATH="$RISCV/include"
export CPLUS_INCLUDE_PATH="$RISCV/include"

# Install Verilator v5.
# Set VERILATOR_INSTALL_DIR to 'NO' to skip installation and checks
# of Verilator (useful for CI jobs not depending on Verilator in any way).
if [ "$VERILATOR_INSTALL_DIR" != "NO" ]; then
  source verif/regress/install-verilator.sh

  # Complain if the installation directory of Verilator still is not set
  # after running the installer.
  if [ -z "$VERILATOR_INSTALL_DIR" ]; then
    echo "Error: VERILATOR_INSTALL_DIR variable still undefined after running Verilator installer."
    return
  fi

  # Verilator was set up: add Verilator paths to appropriate variables.
  export PATH="$VERILATOR_INSTALL_DIR/bin:$PATH"
  export C_INCLUDE_PATH="$VERILATOR_INSTALL_DIR/share/verilator/include:$C_INCLUDE_PATH"
  export CPLUS_INCLUDE_PATH="$VERILATOR_INSTALL_DIR/share/verilator/include:$CPLUS_INCLUDE_PATH"

  echo "Verilator version:"
  verilator --version || { echo "Error: Verilator not in \$PATH." ; return ; }
else
  echo "Skipping Verilator setup on user's request (\$VERILATOR_INSTALL_DIR = \"NO\")."
fi

# number of parallel jobs to use for make commands and simulation
export NUM_JOBS=24

# install the required tools for cva6
if [ -z "$CVA6_REPO" ]; then
  CVA6_REPO="https://github.com/openhwgroup/cva6.git"
  CVA6_BRANCH="master"
  CVA6_HASH="853fb4bee5ca6e36e39dc3c272a97f49d95c3c1d"
  CVA6_PATCH=
fi
echo $CVA6_REPO
echo $CVA6_BRANCH
echo $CVA6_HASH
echo $CVA6_PATCH

# install Spike
if [ -z "$SPIKE_INSTALL_DIR" ]; then
  export SPIKE_INSTALL_DIR=$TOP/spike/
fi
source verif/regress/install-spike.sh
