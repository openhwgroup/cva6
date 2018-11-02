#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="b94c056b137e59deefc62fbfe0cd3a23edfcc07c"

cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if [ ! -e "$RISCV/bin/dtc" ]; then
    echo "Installing DTC"
    git clone https://git.kernel.org/pub/scm/utils/dtc/dtc.git
    cd dtc
    git checkout $VERSION
    make -j${NUM_JOBS} PREFIX=$RISCV/ NO_PYTHON=1
    make -j${NUM_JOBS} check NO_PYTHON=1
    make -j${NUM_JOBS} install PREFIX=$RISCV/ NO_PYTHON=1
else
    echo "Using DTC from cached directory."
fi
