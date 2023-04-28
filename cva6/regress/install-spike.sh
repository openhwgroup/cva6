# Copyright 2021-2023i Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

# Set SPIKE_ROOT to 'NO' to skip the installation/checks of Spike altogether.
# This is useful for CI jobs not depending on Spike in any way.
# Otherwise expect/perform Spike installation in directory $SPIKE_ROOT
# which defaults to $TOP/spike.
if [ -z "$SPIKE_ROOT" ]; then
  # Set the default location if not provided by caller.
  export SPIKE_ROOT=$TOP/spike
fi

if [ "$SPIKE_ROOT" = "NO" ]; then
  echo "Skipping Spike setup on user's request (\$SPIKE_ROOT = \"NO\")."
else
  # Export the location of Spike source code.
  export SPIKE_SRC_DIR=$ROOT_PROJECT/vendor/riscv/riscv-isa-sim

  # Rebuild Spike or reuse an existing Spike build.
  if [ ! -d "$SPIKE_ROOT" -o ! -f "$SPIKE_ROOT/bin/spike"  ]; then
    echo "Installing Spike in '$SPIKE_ROOT'..."
    # Keep track of current working dir.
    CALLER_DIR=$(readlink -f $(pwd))
    # Enter the vectorized tree.  It already captures the desired Spike config.
    cd $SPIKE_SRC_DIR
    # Build and install Spike (including extensions).
    mkdir -p build
    cd build
    ../configure --enable-commitlog --prefix="$SPIKE_ROOT"
    make -j${NUM_JOBS}
    make install
    cd $CALLER_DIR
  else
    echo "Using Spike from cached directory '$SPIKE_ROOT'."
  fi
fi

