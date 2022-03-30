# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume CHAUVON (guillaume.chauvon@thalesgroup.com)

# Program Genesys2 FPGA board connected to $HW_SERVER_URL with bitstream ../work-fpga/ariane_xilinx.bit

open_hw_manager
# Connect to an HW_SERVER connected to the FPGA.
# It is recommended to launch the hw_server before using this script to specify its URL.
connect_hw_server -url $env(HW_SERVER_URL)
open_hw_target
current_hw_device [get_hw_devices xc7k325t_0]
set_property PROGRAM.FILE {../work-fpga/ariane_xilinx.bit} [get_hw_device xc7k325t_0]
program_hw_devices [get_hw_devices xc7k325t_0]
refresh_hw_device [lindex [get_hw_devices xc7k325t_0] 0]
