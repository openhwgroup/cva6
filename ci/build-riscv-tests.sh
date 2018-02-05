#!/bin/sh
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp

[ -d $ROOT/tmp/riscv-tests ] || git clone https://github.com/riscv/riscv-tests.git
cd riscv-tests
git checkout ffa920340430f62e767fb2397f4ee41ffaf441ce
git submodule update --init --recursive
autoconf
mkdir -p build
cd build
../configure --prefix=$ROOT/tmp/riscv-tests/build
make isa -j2
make install

cd isa
# generate hex files
for f in $(ls | grep -v '\.[dump|hex]'); do
    # elf2hex $f
    echo "elf2hex $f > $f.hex"
    elf2hex 8 16384 $f 2147483648 > $f.hex
done
