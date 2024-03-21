#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="920c1379cf6ca2374c6c5207dca425a933d8c7fd"

cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

[ -d $ROOT/tmp/riscv-hyp-tests ] || git clone https://github.com/ninolomata/riscv-hyp-tests
cd riscv-hyp-tests
git checkout $VERSION
git submodule update --init --recursive
make PLAT=cva6