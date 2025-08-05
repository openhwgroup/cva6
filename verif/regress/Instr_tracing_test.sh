#!/bin/bash

# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales

# Usage ./compare_iti_trace.sh <executable>
# Exit 0 if iti traces match, 1 otherwise.

exit_error() {
    echo "$1" >&2
    exit ${2:-1}
}

clean_file_preserve_header() {
    local input_f="$1"
    local output_f="$2"
    local start_skip="$3"
    local end_skip="$4"

    local total_lines lines_to_keep
    total_lines=$(wc -l < "$input_f")
    lines_to_keep=$((total_lines - start_skip - end_skip)) 
 
    if [ "$lines_to_keep" -le 0 ]; then 
        exit_error "Error: not enought lines in $input_f"
    fi

    {
        head -n1 "$input_f"
        tail -n "+$((start_skip + 1))" "$input_f" | head -n "$lines_to_keep"
    } | sed $'s/\r$//'> "$output_f"
}

if [ "$#" -ne 1 ]; then
    exit_error "Usage: $0 <executable>" 2
fi

exe="$1"
base=$(basename "$exe" .o)
mkdir verif/sim/Instr_tracing_artifact
workdir="$(realpath verif/sim/Instr_tracing_artifact)"


if ! bash verif/regress/iti_test.sh "$exe"; then
    exit_error "Error: iti_test.sh failed"
fi

if [ ! -f verif/sim/iti.traces ]; then
    exit_error "Error: iti.traces does not exist"
fi
if [ ! -f verif/sim/encaps.traces ]; then
    exit_error "Error: encaps.traces does not exist"
fi

cp verif/sim/iti.traces "$workdir/iti.trace" 
cp verif/sim/encaps.traces "$workdir/encaps.trace" 

rm verif/sim/iti.traces
rm verif/sim/encaps.traces

cd "$workdir"
git clone https://github.com/riscv-non-isa/riscv-trace-spec.git
cd riscv-trace-spec
git checkout dca761264721068c4576eebd206e2c8b0b9d58b6
cd referenceFlow
bash scripts/build.sh

tmp_riscv="$workdir/riscv-trace-spec/referenceFlow/tests/test_files/$base.riscv"
cd ../../..
cp "$exe" "$tmp_riscv"
cd Instr_tracing_artifact/riscv-trace-spec/referenceFlow
if ! ./scripts/run_regression.sh -t itype3_debug --annotate --debug $tmp_riscv; then
    exit_error "Error: run_regression failed"
fi

reg_dir=$(ls -td ./regression_* 2>/dev/null | head -n1)
if [ -z "$reg_dir" ]; then 
    exit_error "Error: Folder regression does not exist"
fi

iti_out="$reg_dir/itype3_debug/$base.encoder_input"
if [ ! -f "$iti_out" ]; then 
    exit_error "Error: $iti_out does not exist"
fi
encod_out="$reg_dir/itype3_debug/$base.te_inst"
if [ ! -f "$iti_out" ]; then 
    exit_error "Error: $encod_out does not exist"
fi

cp "$iti_out" "$workdir/iti_reg.trace"
cp "$encod_out" "$workdir/encod_reg.trace"

clean_file_preserve_header "$workdir/iti_reg.trace" "$workdir/iti_reg_cleaned.trace" 6 2
clean_file_preserve_header "$workdir/iti.trace" "$workdir/iti_cleaned.trace" 7 0

if diff -q "$workdir/iti_reg_cleaned.trace" "$workdir/iti_cleaned.trace" > /dev/null; then
    echo "SUCESS: Same ITI Traces"
else 
    diff -u "$workdir/iti_reg_cleaned.trace" "$workdir/iti_cleaned.trace"
    exit_error "FAILED: ITI traces do not match"
fi

decapsuler_path="$workdir/../../../corev_apu/instr_tracing/Decapsuler"

if ! make -C "$decapsuler_path"; then
    exit_error "Error: Compilation of Decapsuler failed"
fi

if ! "$decapsuler_path/Decapsuler" "$workdir/encaps.trace"; then
    exit_error "Error: Decapsulation failed"
fi

clean_file_preserve_header "$workdir/encod_reg.trace" "$workdir/encod_reg_cleaned.trace" 3 2
clean_file_preserve_header "$workdir/encaps.csv"  "$workdir/encaps_cleaned.trace"  3 0

if diff -q "$workdir/encod_reg_cleaned.trace" "$workdir/encaps_cleaned.trace"  > /dev/null; then
    echo "SUCESS: Same Encoder Packets"
else 
    python3 "$decapsuler_path/diff_color.py" "$workdir/encaps.csv" "$workdir/encod_reg.trace"
    exit_error "FAILED: Encoder Packets do not match"
fi