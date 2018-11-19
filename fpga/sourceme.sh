#!/bin/bash

# genesys2
if [ -z "${BOARD}" ]; then
    export BOARD="genesys2"
fi

echo -n "Configuring for "

if [ "$BOARD" = "genesys2" ]; then
  echo "Genesys II"
  export XILINX_PART="xc7k325tffg900-2"
  export XILINX_BOARD="digilentinc.com:genesys2:part0:1.1"
  export CLK_PERIOD_NS="20"
fi
