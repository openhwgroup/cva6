#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

export PATH=$RISCV/bin:/bin:$PATH
export LIBRARY_PATH=$RISCV/lib
export LD_LIBRARY_PATH=$RISCV/lib
export C_INCLUDE_PATH=$RISCV/include
export CPLUS_INCLUDE_PATH=$RISCV/include

echo 'deb http://download.opensuse.org/repositories/home:/phiwag:/edatools/xUbuntu_20.04/ /' | sudo tee /etc/apt/sources.list.d/home:phiwag:edatools.list
curl -fsSL https://download.opensuse.org/repositories/home:phiwag:edatools/xUbuntu_20.04/Release.key | gpg --dearmor | sudo tee /etc/apt/trusted.gpg.d/home_phiwag_edatools.gpg > /dev/null
sudo apt update
sudo apt install verilator-4.110 device-tree-compiler

ci/make-tmp.sh
sudo mkdir -p $RISCV && sudo chmod 777 $RISCV
RISCV64_UNKNOWN_ELF_GCC=riscv64-unknown-elf-gcc-8.3.0-2020.04.0-x86_64-linux-ubuntu14.tar.gz
if [ ! -f "$RISCV64_UNKNOWN_ELF_GCC" ]; then
  wget https://static.dev.sifive.com/dev-tools/$RISCV64_UNKNOWN_ELF_GCC
fi
tar -x -f $RISCV64_UNKNOWN_ELF_GCC --strip-components=1 -C $RISCV
ci/install-fesvr.sh
ci/build-riscv-tests.sh
