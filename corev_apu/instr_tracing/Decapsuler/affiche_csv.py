# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales
# Script used to print a csv file in a more readable way
import pandas as pd
import argparse
import os

pd.set_option('display.max_columns',None)
pd.set_option('display.max_rows',None)
pd.set_option("display.width",220)

parser = argparse.ArgumentParser(description="Print the CSV file in a more readable format")
parser.add_argument("--file","-f",required=True, help="CSV file path")
args = parser.parse_args()

csv_path = args.file

if not os.path.isfile(csv_path): 
    print(f"Error '{csv_path}' does not exist")
    exit(1)

df = pd.read_csv(csv_path)

#print(df)

output_filename = os.path.splitext(os.path.basename(csv_path))[0] + "_output.txt"
with open(output_filename, "w",encoding="utf-8") as f: 
    f.write(df.to_string(index=False))