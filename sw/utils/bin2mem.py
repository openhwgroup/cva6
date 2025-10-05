#!/usr/bin/env python

# Copyright (c) 2020 Thales.
# 
# Copyright and related rights are licensed under the Apache
# License, Version 2.0 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# https://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# Author:         Sebastien Jacq - sjthales on github.com
#
# Additional contributions by:
#
#
# script Name:    bin2mem
# Project Name:   CVA6 softcore
# Language:       Python
#
# Description:    Script to generate mem data file for simulation from binary 
#                 application file.
#
# =========================================================================== #
# Revisions  :
# Date        Version  Author       Description
# 2020-10-06  0.1      S.Jacq       Created
# =========================================================================== #

import sys
import math
import binascii

###############################################################################
# Start of file
###############################################################################
if(len(sys.argv) < 2):
    print("Usage bin2mem.py FILENAME")
    quit()

filename = sys.argv[1].strip('.bin') + ".mem"

mem_file  = open(filename,    'wb')

with open(sys.argv[1], "rb") as f:
    bytes_read = f.read(8)
    while bytes_read:
        bytes_read_inv = bytes_read[::-1]
        mem_file.write(b"%s\n" %binascii.hexlify(bytes_read_inv) )
        bytes_read = f.read(8)
    
###############################################################################
# close all files
###############################################################################

mem_file.close()

