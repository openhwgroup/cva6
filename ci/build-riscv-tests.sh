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

cd isa
# generate hex files
if [ $(command -v elf2hex) > /dev/null ]; then
    for f in $(ls | grep -v '\.[dump|hex]'); do
        # elf2hex $f
        echo "elf2hex $f > $f.hex"
        elf2hex 8 16384 $f 2147483648 > $f.hex
    done
else
    echo "Skipping hex file generation"
fi
