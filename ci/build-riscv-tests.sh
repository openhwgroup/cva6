#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="19760b7a7d72227376d91b1afb0f13915c233efb"

cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

[ -d $ROOT/tmp/riscv-tests ] || git clone https://github.com/pulp-platform/riscv-tests.git
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
