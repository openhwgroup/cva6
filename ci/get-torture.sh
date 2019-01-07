#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
VERSION="59b0f0f224ff4f1eb6ebb1b4dd7eaf1ab3fac2e5"

cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

[ -d $ROOT/tmp/riscv-torture ] || git clone https://github.com/ucb-bar/riscv-torture.git
cd riscv-torture
git checkout $VERSION
git submodule update --init --recursive

# copy ariane specific config
cp config/default.config config/default.config.bak
cp $ROOT/ci/default.config config/default.config
git checkout ./output/Makefile
git apply $ROOT/ci/torture_make.patch

