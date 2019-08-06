#!/usr/bin/env python3

from string import Template
import argparse
import os.path
import sys
import binascii

romsize = 2**13 # 8192

parser = argparse.ArgumentParser(description='Convert binary file to verilog rom')
parser.add_argument('filename', metavar='filename', nargs=1, help='filename of input binary')

args = parser.parse_args()
file = args.filename[0];

# check that file exists
if not os.path.isfile(file):
  print("File {} does not exist.".format(filename))
  sys.exit(1)

filename = os.path.splitext(file)[0]

def read_bin():

  with open(filename + ".img", 'rb') as f:
    rom = binascii.hexlify(f.read())
    rom = map(''.join, zip(rom[::2], rom[1::2]))

  # align to 64 bit
  align = (int((len(rom) + 7) / 8 )) * 8;

  for i in range(len(rom), align):
    rom.append("00")

  return rom

rom = read_bin()

""" Generate mem file of bootcode for bram update
"""
with open(filename + ".mem", "w") as f:
  rom_str = "@0000\n"

  # process in junks of 64 bit (8 byte)
  for i in range(int(len(rom)/8)):
    rom_str += "".join(rom[i*8  :i*8+8]) + "\n"

  for i in range(int((romsize - len(rom))/8)):
    rom_str += "0000000000000000\n"
      
  f.write(rom_str)

  f.close()