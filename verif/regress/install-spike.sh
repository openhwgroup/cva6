# Copyright 2021-2023 Thales DIS design services SAS
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

# Set SPIKE_INSTALL_DIR to 'NO' to skip the installation/checks of Spike
# altogether.
# This is useful for CI jobs not depending on Spike in any way.
# Otherwise expect/perform Spike installation in directory $SPIKE_INSTALL_DIR
# which defaults to $ROOT_PROJECT/tools/spike.
if [ -z "$SPIKE_INSTALL_DIR" ]; then
  # Set the default location if not provided by caller.
  export SPIKE_INSTALL_DIR=$ROOT_PROJECT/tools/spike
fi

if [ "$SPIKE_INSTALL_DIR" = "NO" ]; then
  echo "NOTE: Skipping Spike setup on user's request (\$SPIKE_INSTALL_DIR = \"NO\")."
else
  # Export the location of Spike source code.  Assume we are located in CVA6_TOP/verif/regress.
  ROOT_PROJECT=$(readlink -f $(dirname $0))/../..
  export SPIKE_SRC_DIR=$ROOT_PROJECT/vendor/riscv/riscv-isa-sim

  # Check if a local copy of Spike should be built/used ($SPIKE_INSTALL_DIR non empty).
  # A value equal to '__local__' means $ROOT_PROJECT/tools/spike (same as $TOP/spike).
  if [ -n "$SPIKE_INSTALL_DIR" ]; then
      # Handle the 'default' value.
      if [ "$SPIKE_INSTALL_DIR" = "__local__" ]; then
        export SPIKE_INSTALL_DIR="$ROOT_PROJECT/tools/spike"
      fi
      # Override SPIKE_ROOT value with $SPIKE_INSTALL_DIR (the latter takes priority.)
      # TODO: Remove the following two lines when SPIKE_ROOT is phased out.
      echo "NOTE: Overriding SPIKE_ROOT value ('$SPIKE_ROOT') with \$SPIKE_INSTALL_DIR ('$SPIKE_INSTALL_DIR')."
      export SPIKE_ROOT="$SPIKE_INSTALL_DIR"
      # Do not clean up the destination directory: leave that to the user (real or CI job).
  fi

  # Rebuild Spike or reuse an existing Spike build.
  if [ ! -d "$SPIKE_INSTALL_DIR" -o ! -f "$SPIKE_INSTALL_DIR/bin/spike" ]; then
    echo "Installing Spike in '$SPIKE_INSTALL_DIR'..."
    # Keep track of current working dir.
    CALLER_DIR=$(readlink -f $(pwd))
    # Enter the vendorized tree.  It already captures the desired Spike config.
    cd $SPIKE_SRC_DIR
    # Build and install Spike (including extensions).
    mkdir -p build
    cd build
    ../configure --enable-commitlog --prefix="$SPIKE_INSTALL_DIR"
    make -j${NUM_JOBS}
    make install
    cd $CALLER_DIR
  else
    echo "Using Spike from cached directory '$SPIKE_INSTALL_DIR'."
  fi
fi

