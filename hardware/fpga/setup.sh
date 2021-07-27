#!/bin/bash

export VIVADO_HOME=/opt/xilinx/Vivado/2018.2
source $VIVADO_HOME/settings64.sh

#VIVADO SETTINGS
#Settings are board specific. Check FPGA board datasheet to add new target
# either "vcu118" or "zcu102"

if [ -z "$BOARD"  ]; then
    read -p "Which board you want to use:  1-zcu102 2-vcu118: " BOARD

    if [ "$BOARD" = "1" ]; then
        export BOARD="zcu102"
        export XILINX_PART="xczu9eg-ffvb1156-2-e"
        export XILINX_BOARD="xilinx.com:zcu102:part0:3.2"
    elif [ "$BOARD" = "2" ]; then
        export BOARD="vcu118"
        export XILINX_PART="xcvu9p-flga2104-2L-e"
        export XILINX_BOARD="xilinx.com:vcu118:part0:2.0"
    fi
fi

echo "$BOARD"
echo "XILINX_PART=$XILINX_PART"
echo "XILINX_BOARD=$XILINX_BOARD"

export VSIM_PATH=$PWD/sim
