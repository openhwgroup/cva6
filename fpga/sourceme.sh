#!/bin/bash

# genesys2
if [ -z "${BOARD}" ]; then
    export BOARD="genesys2"
fi

if [ "$BOARD" = "genesys2" ]; then
  echo -n "Configuring for "
  echo "Genesys II"
  export XILINX_PART="xc7k325tffg900-2"
  export XILINX_BOARD="digilentinc.com:genesys2:part0:1.1"
  export CLK_PERIOD_NS="20"
fi

if [ "$BOARD" = "kc705" ]; then
  echo -n "Configuring for "
  echo "Kintex kc705"
  export XILINX_PART="xc7k325tffg900-2"
  export XILINX_BOARD="xilinx.com:kc705:part0:1.5"
  export CLK_PERIOD_NS="20"
fi

if [ "$BOARD" = "vc707" ]; then
  echo -n "Configuring for "
  echo "Virtex vc707"
  export XILINX_PART="xc7vx485tffg1761-2"
  export XILINX_BOARD="xilinx.com:vc707:part0:1.3"
  export CLK_PERIOD_NS="20"
fi
