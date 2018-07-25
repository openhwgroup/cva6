#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp
RELEASE=0.1.0

if ! [ -e $ROOT/tmp/riscv-fesvr ]; then
    git clone https://github.com/riscv/riscv-fesvr.git
fi
cd $ROOT/tmp/riscv-fesvr
mkdir -p build
cd build
../configure --prefix="$ROOT/tmp"
make -j2
make install
