#!/bin/env python3
# Copyright 2023 Commissariat a l'Energie Atomique et aux Energies
#                Alternatives (CEA)
#
# Licensed under the Solderpad Hardware License, Version 2.1 (the “License”);
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Authors: Cesar Fuguet
# Date: October, 2023
# Description: script to flatten a Flist file. Flattening consist on:
#   -  expanding environment variables in the file
#   -  expanding included Flist files

import sys;
import argparse;
import os;

def printLine(outf, line, printNewline):
    if printNewline:
        outf.write(f'{line}\n')
    else:
        outf.write(line + ' ')

def parseFlist(inFlist, outFlist, printIncdir, printNewline):
    lines = iter(inFlist.read().splitlines())
    for line in lines:
        line = line.strip()
        if (line.startswith('#') or
                line.startswith('//') or
                line.startswith('/*')):
            continue
        line = os.path.expandvars(line)
        if line.startswith('+incdir+'):
            if printIncdir:
                printLine(outFlist, line, printNewline)
        elif line.startswith('-F'):
            includedFilename = line.lstrip('-F').strip()
            if not os.path.exists(includedFilename):
                raise (RuntimeError(f'{includedFilename} not found'))
            with open(includedFilename, 'r') as includedFlist:
                parseFlist(includedFlist, outFlist, printIncdir, printNewline)
        elif line:
            printLine(outFlist, line, printNewline)


def getArguments():
    parser = argparse.ArgumentParser(description='Flatten a Flist file')
    parser.add_argument(
            '--print_incdir',
            action="store_true",
            help='Print incdir statements in the output')
    parser.add_argument(
            '--print_newline',
            action="store_true",
            help='Print newline in the output after each line')
    parser.add_argument(
            'inFlist',
            nargs='?',
            type=argparse.FileType('r'),
            default=sys.stdin,
            help='Input Flist file (default to stdin)')
    parser.add_argument(
            'outFlist',
            nargs='?',
            type=argparse.FileType('w'),
            default=sys.stdout,
            help='Output flattened Flist file (default to stdout)')
    return parser.parse_args()


if __name__ == "__main__":
    args = getArguments()
    parseFlist(args.inFlist, args.outFlist, args.print_incdir, args.print_newline)
