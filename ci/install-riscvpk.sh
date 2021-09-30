#!/bin/bash

set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
PATH=$RISCV/bin:/bin:$PATH

cd $ROOT/tmp

echo "Installing RISC-V Proxy Kernel and Boot Loader"
git clone https://github.com/riscv-software-src/riscv-pk.git
cd riscv-pk
mkdir -p build
cd build
../configure --prefix=$RISCV --host=riscv64-unknown-elf
make
make install
