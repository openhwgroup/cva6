#!/usr/bin/env bash

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