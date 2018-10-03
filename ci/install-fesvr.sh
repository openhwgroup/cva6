#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION=30e85ce253788b29bd4ac0b5e5c23a077d96dc24

cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if [ ! -e "${RISCV}/lib/libfesvr.so"  ]; then
    echo "Installing RISCV FESVR"
    git clone https://github.com/riscv/riscv-fesvr.git
    cd riscv-fesvr
    git checkout $VERSION
    mkdir -p build
    cd build
    ../configure --prefix="$RISCV/"
    make -j${NUM_JOBS}
    make install
else
    echo "Using RISCV FESVR from cached directory."
fi



