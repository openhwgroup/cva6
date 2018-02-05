#!/bin/sh
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp

[ -d $ROOT/tmp/riscv-gnu-toolchain ] || git clone https://github.com/riscv/riscv-gnu-toolchain.git
cd riscv-gnu-toolchain
git checkout 691e4e826251c7ec59f883cab18440c87baf45e7
git submodule update --init --recursive

mkdir -p $RISCV

./configure --prefix=$RISCV
make -j2
