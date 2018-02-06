#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp

if [ ! -e "$ROOT/tmp/bin/verilator" ]; then
    echo "Installing Verilator"
    wget https://www.veripool.org/ftp/verilator-3.918.tgz
    tar xzf verilator*.t*gz && cd verilator-*
    autoconf && ./configure --prefix="$ROOT/tmp" && make -j2 && make test && make install
else
    echo "Using Verilator from cached directory."
fi
