#!/bin/bash
# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume CHAUVON (guillaume.chauvon@thalesgroup.com)


BITSTREAM=../work-fpga/ariane_xilinx.bit

if ! [ -n "$VIVADO_CMD" ]; then
  echo "Error: VIVADO_CMD variable undefined.
It most likely should be VIVADO_CMD=vivado_lab if you installed 2022's version of vivado."
  return
fi

if [ -f "$BITSTREAM" ]; then
    $VIVADO_CMD -mode batch -source program_genesys2.tcl &&\
    python3 linux_boot.py
fi
