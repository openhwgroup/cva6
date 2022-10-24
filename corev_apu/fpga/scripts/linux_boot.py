# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume CHAUVON (guillaume.chauvon@thalesgroup.com)

# Check that linux boots by reading FPGA's UART.
# If linux does not boot, this script will loop infinitely so it is recommended to kill it.
# In Thales-CI it is killed from the timeout of the job triggering it.

import sys
import serial
import os


ser = serial.Serial(os.getenv("UART_SERIAL"), 115200, timeout=60)
ser.baudrate = 115200

with open("fpga_boot.rpt", "w") as f:
    while True:
        firstChar = ser.read().decode("utf-8")
        line = ser.readline().decode("utf-8")
        print(firstChar + line, end="")
        f.write(firstChar + line)
        # Check for command prompt
        if firstChar == "#" and line == " ":
            ser.write(b"uname -a\n")
        elif firstChar == "" and line == "":
            sys.exit(1)
            break
        if ("Linux buildroot" in firstChar + line) and (
            "riscv" in firstChar + line
        ):
            break

print("Successful Linux boot !")
ser.close()
sys.exit(0)
