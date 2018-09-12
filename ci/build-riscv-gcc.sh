#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="691e4e826251c7ec59f883cab18440c87baf45e7"
cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if ! [ -e $RISCV/bin ]; then
    [ -d $ROOT/tmp/riscv-gnu-toolchain ] || git clone https://github.com/riscv/riscv-gnu-toolchain.git
    cd riscv-gnu-toolchain
    git checkout $VERSION
    git submodule update --init --recursive

    mkdir -p $RISCV

    echo "Compiling RISC-V Toolchain"
    ./configure --prefix=$RISCV > /dev/null
    make -j${NUM_JOBS} > /dev/null
    echo "Compilation Finished"
fi
