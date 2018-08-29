#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp
RELEASE=0.1.0

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if ! [ -e $ROOT/tmp/riscv-fesvr ]; then
    git clone https://github.com/riscv/riscv-fesvr.git
fi
cd $ROOT/tmp/riscv-fesvr
mkdir -p build
cd build
../configure --prefix="$ROOT/tmp"
make -j${NUM_JOBS}
make install
