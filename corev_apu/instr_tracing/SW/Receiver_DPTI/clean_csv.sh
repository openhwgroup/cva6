#!/usr/bin/env bash
# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales
# THis script remove lines above the start packet 3.3

if [ $# -ne 1 ]; then
    echo "Usage!: $0 file/to/clean.csv"
    exit 1
fi
# This script will clean the csv trace by starting the trace at the first packet after reset
input_file="$1"
output_file="${input_file%.csv}_cleaned.csv"
temp_file=$(mktemp)

awk 'found || /^3,3,_,_,/ {found=1; print}' "$input_file" > "$temp_file"

{
    printf "format,subformat,address,branch,branches,branch_map,branch_count,"
    printf "branch_fmt,context,ecause,ienable,encoder_mode,interrupt,irreport,"
    printf "irdepth,notify,ioptions,privilege,qual_status,time,thaddr,tval,"
    printf "updiscon,denable,dloss,doptions\n"

    cat "$temp_file"
} > "$output_file"

rm "$temp_file"

echo "File Cleaned : $output_file"