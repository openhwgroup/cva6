#!/usr/bin/env python3

# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon (guillaume.chauvon@thalesgroup.com)

import sys
import os
import argparse
import re

def setup_parser_config_generator():
  parser = argparse.ArgumentParser()

  parser.add_argument("--default_config", type=str, default="cv64a6_imafdc_sv39", required=True,
                      choices=["cv32a6_imac_sv0","cv32a6_imac_sv32","cv32a6_imafc_sv32","cv64a6_imafdc_sv39","cv32a60x"],
                      help="Default configuration is one of the 4 preexisting configuration: \
                            cv32a6_imac_sv0, cv32a6_imac_sv32, cv32a6_imafc_sv32, cv64a6_imafdc_sv39")
  parser.add_argument("--isa", type=str, default=None, required=True,
                      help="RISC-V ISA subset")
  parser.add_argument("--fpu", type=int, default=None, choices=[0,1],
                      help="FPU enable ? 1 : enable, 0 : disable")
  parser.add_argument("--F16En", type=int, default=None, choices=[0,1],
                      help="F16En enable ? 1 : enable, 0 : disable")
  parser.add_argument("--F16AltEn", type=int, default=None, choices=[0,1],
                      help="F16AltEn enable ? 1 : enable, 0 : disable")
  parser.add_argument("--F8En", type=int, default=None, choices=[0,1],
                      help="F8En enable ? 1 : enable, 0 : disable")
  parser.add_argument("--FVecEn", type=int, default=None, choices=[0,1],
                      help="FVecEn enable ? 1 : enable, 0 : disable")
  parser.add_argument("--cvxif", type=int, default=None, choices=[0,1],
                      help="CoreV-X-Interface enable ? 1 : enable, 0 : disable")
  parser.add_argument("--c_ext", type=int, default=None, choices=[0,1],
                      help="C extension enable ? 1 : enable, 0 : disable")
  parser.add_argument("--a_ext", type=int, default=None, choices=[0,1],
                      help="A extension enable ? 1 : enable, 0 : disable")
  parser.add_argument("--iuser_en", type=int, default=None, choices=[0,1],
                      help="Fetch User enable ? 1 : enable, 0 : disable")
  parser.add_argument("--iuser_w", type=int, default=None, choices=list(range(1,64)),
                      help="Fetch User Width ? [1-64]")
  parser.add_argument("--duser_en", type=int, default=None, choices=[0,1],
                      help="Data User enable ? 1 : enable, 0 : disable")
  parser.add_argument("--duser_w", type=int, default=None, choices=list(range(1,64)),
                      help="Data User Width ? [1-64]")
  parser.add_argument("--RenameEn", type=int, default=None, choices=[0,1],
                      help="RenameEn ? 1 : enable, 0 : disable")
  return parser

ISA = ""
MABI = ""
Config = dict()

MapArgsToParameter={
  "xlen" : "CVA6ConfigXlen",
  "fpu" : "CVA6ConfigFpuEn",
  "F16En" : "CVA6ConfigF16En",
  "F16AltEn" : "CVA6ConfigF16AltEn",
  "F8En" : "CVA6ConfigF8En",
  "FVecEn" : "CVA6ConfigFVecEn",
  "cvxif" : "CVA6ConfigCvxifEn",
  "c_ext" : "CVA6ConfigCExtEn",
  "a_ext" : "CVA6ConfigAExtEn",
  "iuser_en" : "CVA6ConfigFetchUserEn",
  "iuser_w" : "CVA6ConfigFetchUserWidth",
  "duser_en" : "CVA6ConfigDataUserEn",
  "duser_w" : "CVA6ConfigDataUserWidth",
  "RenameEn" : "CVA6ConfigRenameEn",
}
MapParametersToArgs = {i:k for k, i in MapArgsToParameter.items()} #reverse map

def generate_config(argv):
  parser = setup_parser_config_generator()
  args = parser.parse_args(argv)
  Args = vars(args) # give a dictionary of args
  print("\n[Generating configuration ... ]")
  print("Default configuration is "+Args['default_config'])
  print("Make sure to compile your code with this ISA :", Args["isa"], "!")
  ISA = Args["isa"]
  if "cv32" in Args['default_config']:
    gen = "gen32"
    Args['xlen'] = 32
    MABI = "ilp32"
  else:
    gen = "gen64"
    Args['xlen'] = 64
    MABI = "lp64"
  os.system("cp core/Flist."+Args['default_config']+" core/Flist."+gen) #copy Flist
  os.system("cp core/include/"+Args['default_config']+"_config_pkg.sv core/include/"+gen+"_config_pkg.sv") # copy package
  Flistfile = open("core/Flist."+gen, "r")
  Flistlines = []
  for line in Flistfile :
    line = re.sub(r"(\${CVA6_REPO_DIR}/core/include/)"+Args['default_config']+"(_config_pkg.sv)", r"\g<1>"+gen+"\g<2>", line) # change package name in Flist to the one generated
    Flistlines.append(line)
  Flistfile = open("core/Flist."+gen, "w")
  Flistfile.writelines(Flistlines)
  Flistfile.close
  for i in Args:
    configfile = open("core/include/"+gen+"_config_pkg.sv", "r")
    if i not in ['default_config', 'isa', 'xlen']:
      if Args[i] != None:
        print("setting", i, "to", Args[i])
        alllines = []
        lineXlen = None
        for line in configfile :
          lineXlen = re.match(r"(    localparam CVA6ConfigXlen = )(?P<value>.*)(;)", line) if lineXlen == None else lineXlen
          line = re.sub(r"(    localparam "+MapArgsToParameter[i]+" = )(.*)(;)", r"\g<1>"+str(Args[i])+"\g<3>", line) # change parameter if required by Args
          alllines.append(line)
          linematch = re.match(r"(    localparam (CVA6Config)(?P<param>.*) = )(?P<value>.*)(;)", line) # and read the modified line to know which configuration we are creating
          if linematch:
            Param = MapParametersToArgs['CVA6Config'+linematch.group('param')]
            Config[Param] = lineXlen.group('value') if linematch.group('value') == "CVA6ConfigXlen" else linematch.group('value')
            for k in Config.keys():
              Config[k] = int(Config[k]) # Convert value from str to int
        configfile = open("core/include/"+gen+"_config_pkg.sv", "w")
        configfile.writelines(alllines)
  configfile.close
  print("[Generating configuration Done]")
  return [ISA, MABI, gen, Config] # return ISA, MABI, gen (for testharness), Config for cva6.py in core-v-verif


if __name__ == "__main__":
  generate_config(sys.argv[1:])
