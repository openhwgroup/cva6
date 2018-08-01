#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp

[ -d $ROOT/tmp/riscv-tests ] || git clone https://github.com/riscv/riscv-tests.git
cd riscv-tests
git checkout 294bfce8a1ca2fc501b8939292146e44f813a2b8
git submodule update --init --recursive
autoconf
mkdir -p build
cd build
../configure --prefix=$ROOT/tmp/riscv-tests/build
make isa -j2 > /dev/null
make install
