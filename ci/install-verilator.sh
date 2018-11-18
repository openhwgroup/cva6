#!/bin/bash
set -e
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd $ROOT/tmp

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if [ ! -e "$VERILATOR_ROOT/bin/verilator" ]; then
    echo "Installing Verilator"
    wget https://www.veripool.org/ftp/verilator-3.924.tgz
    tar xzf verilator*.t*gz 
    rm verilator*.t*gz 
    cd verilator-*
    mkdir -p $VERILATOR_ROOT
    # copy scripts
    autoconf && ./configure --prefix="$VERILATOR_ROOT" && make -j${NUM_JOBS} 
    cp -r * $VERILATOR_ROOT/ 
    make test
else
    echo "Using Verilator from cached directory."
fi
