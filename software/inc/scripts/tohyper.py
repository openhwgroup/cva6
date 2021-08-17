#!/usr/bin/python3

#Written by ABA to update the format of the slm file to be compliant with hyperflash model used in testbench
import numpy as np
import os
import os.path
import argparse
import sys

parser = argparse.ArgumentParser(description='Generate hyper memory image file from slm')

parser.add_argument("--input", dest="input_file", default=None, help="Specify input file (ex. ./build/pulpissimo/slm_files/flash_stim.slm)")
parser.add_argument("--output", dest="output_file", default=None, help="Specify output file (ex. ./build/pulpissimo/slm_files/hyper_flash_stim.slm)")

args = parser.parse_args()

if args.input_file is None:
    raise Exception('Specify the input file with --input=<path> (ex. --input=./build/pulpissimo/slm_files/flash_stim.slm)')

if args.output_file is None:
    raise Exception('Specify the output file with --output=<path> (ex. --output=./build/pulpissimo/slm_files/hyper_flash_stim.slm')

delimiter=" "
with open(args.input_file, "rU") as fi:
    data = list(map(lambda x:x.split("_"), fi.read().strip().split("\n")))
fo=open(args.output_file, "w")
A=np.array(data)
print(A[0][1])
for i in range(0, A.shape[0],2):
    fo.write('@%s %s\n' %(A[i][0],A[i][1]))
