# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

set -e
VERSION="59a9277ac1e3f9aca630fb035d1dbacaa091e375"

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if [ ! -f "$SPIKE_ROOT/bin/spike"  ]; then
    echo "Installing Spike"
    PATCH_DIR=`pwd`/cva6/regress
    mkdir -p $SPIKE_ROOT
    cd $SPIKE_ROOT
    git clone https://github.com/riscv/riscv-isa-sim.git 
    cd riscv-isa-sim
    git checkout $VERSION
    git apply $PATCH_DIR/spike-shared-fesvr-lib.patch
    mkdir -p build
    cd build
    ../configure --enable-commitlog --prefix="$SPIKE_ROOT"
    make -j${NUM_JOBS}
    make install
else
    echo "Using Spike from cached directory."
fi



