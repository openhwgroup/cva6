#!/usr/bin/env bash 
# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales

set -euo pipefail

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <file1_raw> <file2_ref>"
    exit 2
fi

dir_work="encoder_log"
rm -rf "$dir_work"
mkdir -p "$dir_work"

trace_raw_path="$1"
trace_ref_path="$2"


base_raw=$(basename "$trace_raw_path")
base_ref=$(basename "$trace_ref_path")


for trace in "$trace_raw_path" "$trace_ref_path"; do 
    if [ ! -f "$trace" ]; then
        echo "ERROR file '$trace' does not exist"
        exit 1
    fi 
    base=$(basename "$trace")
    cp "$trace" "$dir_work/$base"
done

trace_raw="$dir_work/$base_raw"
trace_ref="$dir_work/$base_ref"

./Decapsuler "$trace_raw"

python3 affiche_csv.py -f "$dir_work/${base_raw%.txt}.csv"
mv "${base_raw%.txt}_output.txt" "$dir_work"
python3 affiche_csv.py -f "$trace_ref"
mv "${base_ref%.te_inst}_output.txt" "$dir_work"


python3 diff_color.py "$dir_work/${base_raw%.txt}.csv" "$trace_ref"

 