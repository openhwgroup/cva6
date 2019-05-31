#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if [ ! -e "$VERILATOR_ROOT/bin/verilator" ]; then
    echo "Installing Verilator"
    rm -f verilator*.tgz
    wget https://www.veripool.org/ftp/verilator-4.014.tgz
    tar xzf verilator*.tgz
    rm -f verilator*.tgz
    cd verilator-4.014
    mkdir -p $VERILATOR_ROOT
    # copy scripts
    autoconf && ./configure --prefix="$VERILATOR_ROOT" && make -j${NUM_JOBS}
    cp -r * $VERILATOR_ROOT/
    make test
else
    echo "Using Verilator from cached directory."
fi
