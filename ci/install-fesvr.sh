#!/bin/sh
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp
RELEASE=0.1.0

if ! [ -e $ROOT/tmp/riscv-fesvr-$RELEASE ]; then
    wget https://github.com/pulp-platform/riscv-fesvr/archive/v$RELEASE.tar.gz
    tar xzf v$RELEASE.tar.gz
fi
cd $ROOT/tmp/riscv-fesvr-$RELEASE
mkdir -p build
cd build
../configure --prefix="$ROOT/tmp"
make -j2
make install
