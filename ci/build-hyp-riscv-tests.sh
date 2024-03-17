#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="b0fab83d72d7639a12cc37715baed1f44568d19f"

cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

[ -d $ROOT/tmp/riscv-hyp-tests ] || git clone https://github.com/ninolomata/riscv-hyp-tests
cd riscv-hyp-tests
git checkout $VERSION
git submodule update --init --recursive
make PLAT=cva6