# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales


import csv
import sys
import re

def gray(s): return f"\033[90m{s}\033[0m"
def red(s): return f"\033[91m{s}\033[0m"
def green(s): return f"\033[92m{s}\033[0m"
def white(s): return f"\033[97m{s}\033[0m"

ANSI_ESCAPE= re.compile

def strip(text):
    return re.sub(r'\x1b\[[0-9;]*m','',text)

def read_csv_to_matrix(filepath):
    with open(filepath,newline='') as csvfile:
        reader = csv.reader(csvfile,delimiter=',')
        rows = list(reader)
    header = rows[0]
    data = rows[1:]
    return header,data



def format_value(val_gen, val_ref):
    if val_gen is None:
        return f"{red('NDF')}{white(' -> ')}{green(val_ref)}"
    elif val_gen == val_ref:
        return gray(val_gen)
    else: 
        return f"{red(val_gen)}{white(' -> ')}{green(val_ref)}"
    
def compare_matrices(header,gen_data,ref_data):
    max_rows = max(len(gen_data),len(ref_data))
    num_cols = len(header)
    result_matrix = [[None for _ in range (num_cols)] for _ in range(max_rows)]

    for row_idx in range(max_rows):
        for col_idx in range(num_cols):
            try: 
                val_ref = ref_data[row_idx][col_idx]
            except IndexError:
                val_ref=""
            try: 
                val_gen = gen_data[row_idx][col_idx]
            except IndexError:
                val_gen=None
            result_matrix[row_idx][col_idx] = format_value(val_gen,val_ref)

    return result_matrix

def print_column_by_column(header,matrix,cols_per_block=8):
    num_cols = len(header)
    num_rows = len(matrix)

    for block_start in range(0,num_cols, cols_per_block):
        block_end = min(block_start + cols_per_block,num_cols)
        block_indices = range(block_start,block_end)

        col_widths =[]
        for i in block_indices:
            max_len = max(len(strip(matrix[r][i])) for r in range(num_rows))
            max_len = max(max_len, len(header[i]))
            col_widths.append(max_len + 2)
        header_line =""
        for i,w in zip(block_indices,col_widths):
            header_line += header[i].center(w) + "  "
        print(header_line)

        for r in range(num_rows):
            row_line = ""
            for i,w in zip(block_indices,col_widths):
                content = matrix[r][i]
                pad_len = w - len(strip(content))
                left_pad = pad_len // 2
                right_pad = pad_len - left_pad  
                row_line += " "*left_pad + content + " "*right_pad + "  "
            print(row_line)

        print("\n")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("usage : diff.py <generated_output> <reference_output>")
        sys.exit(1)
    
    gen_path = sys.argv[1]
    ref_path = sys.argv[2]

    gen_header, gen_data = read_csv_to_matrix(gen_path)
    ref_header , ref_data = read_csv_to_matrix(ref_path)

    matrix = compare_matrices(ref_header,gen_data,ref_data)
    print_column_by_column(ref_header,matrix,cols_per_block=14)
