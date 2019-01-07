#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="7cc76ea83b4f827596158c8ba0763e93da65de8f"

cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

[ -d $ROOT/tmp/riscv-tests ] || git clone https://github.com/riscv/riscv-tests.git
cd riscv-tests
git checkout $VERSION
git submodule update --init --recursive
autoconf
mkdir -p build
cd build
../configure --prefix=$ROOT/tmp/riscv-tests/build
make isa        -j${NUM_JOBS} > /dev/null
make benchmarks -j${NUM_JOBS} > /dev/null
make install
