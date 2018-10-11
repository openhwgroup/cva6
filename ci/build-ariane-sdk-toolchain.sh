#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="59a47b57278c541b34019bbb019a4f66654b533f"
cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if ! [ -e $RISCV/bin ]; then
    [ -d $ROOT/tmp/ariane-sdk ] || git clone https://github.com/pulp-platform/ariane-sdk.git
    cd ariane-sdk
    git checkout master
    git pull
    git checkout $VERSION
    git submodule update --init --recursive riscv-gnu-toolchain

    mkdir -p $RISCV

    echo "Bulding ariane-sdk"
    echo "make NR_CORES=${NUM_JOBS} RISCV=${RISCV}"
    make NR_CORES=${NUM_JOBS} RISCV=${RISCV} gnu-toolchain-newlib > /dev/null
    echo "Compilation Finished"
else
    echo "Using ariane-sdk from cached directory."
fi
