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
  parser.add_argument("--IcacheByteSize", type=int, default=None,
                      help="Instruction cache size in bytes")
  parser.add_argument("--IcacheSetAssoc", type=int, default=None,
                      help="Instruction cache associativity")
  parser.add_argument("--IcacheLineWidth", type=int, default=None,
                      help="Instruction cache line width")
  parser.add_argument("--DcacheByteSize", type=int, default=None,
                      help="Data cache size in bytes")
  parser.add_argument("--DcacheSetAssoc", type=int, default=None,
                      help="Data cache associativity")
  parser.add_argument("--DcacheLineWidth", type=int, default=None,
                      help="Data cache line width")
  parser.add_argument("--DcacheIdWidth", type=int, default=None,
                      help="Data cache TID width")
  parser.add_argument("--MemTidWidth", type=int, default=None,
                      help="Memory TID width")
  parser.add_argument("--WtDcacheWbufDepth", type=int, default=None,
                      help="WT data cache WBUF depth")
  parser.add_argument("--NrCommitPorts", type=int, default=None, choices=[1,2],
                      help="Number of commit ports")
  parser.add_argument("--NrScoreboardEntries", type=int, default=None,
                      help="Number of scoreboard entries")
  parser.add_argument("--FPGAEn", type=int, default=None, choices=[0,1],
                      help="Use FPGA-specific hardware")
  parser.add_argument("--NrLoadPipeRegs", type=int, default=None,
                      help="Load latency")
  parser.add_argument("--NrStorePipeRegs", type=int, default=None,
                      help="Store latency")
  parser.add_argument("--InstrTlbEntries", type=int, default=None,
                      help="Number of instruction TLB entries")
  parser.add_argument("--DataTlbEntries", type=int, default=None,
                      help="Number of data TLB entries")
  parser.add_argument("--RASDepth", type=int, default=None,
                      help="Depth of Return Address Stack")
  parser.add_argument("--BTBEntries", type=int, default=None,
                      help="Number of Branch Target Buffer entries")
  parser.add_argument("--BHTEntries", type=int, default=None,
                      help="Number of Branch History Table entries")
  parser.add_argument("--NrPMPEntries", type=int, default=None,
                      help="Number of PMP entries")
  parser.add_argument("--PerfCounterEn", type=int, default=None,
                      help="Enable performance counters")
  parser.add_argument("--DcacheType", type=str, default=None, choices=["WB", "WT"],
                      help="Cache type (WB or WT)")
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
  "IcacheByteSize" : "CVA6ConfigIcacheByteSize",
  "IcacheSetAssoc" : "CVA6ConfigIcacheSetAssoc",
  "IcacheLineWidth" : "CVA6ConfigIcacheLineWidth",
  "DcacheByteSize" : "CVA6ConfigDcacheByteSize",
  "DcacheSetAssoc" : "CVA6ConfigDcacheSetAssoc",
  "DcacheLineWidth" : "CVA6ConfigDcacheLineWidth",
  "DcacheIdWidth" : "CVA6ConfigDcacheIdWidth",
  "DcacheIdWidth": "CVA6ConfigDcacheIdWidth",
  "MemTidWidth": "CVA6ConfigMemTidWidth",
  "WtDcacheWbufDepth": "CVA6ConfigWtDcacheWbufDepth",
  "NrCommitPorts" : "CVA6ConfigNrCommitPorts",
  "NrScoreboardEntries" : "CVA6ConfigNrScoreboardEntries",
  "FPGAEn" : "CVA6ConfigFPGAEn",
  "NrLoadPipeRegs" : "CVA6ConfigNrLoadPipeRegs",
  "NrStorePipeRegs" : "CVA6ConfigNrStorePipeRegs",
  "InstrTlbEntries" : "CVA6ConfigInstrTlbEntries",
  "DataTlbEntries" : "CVA6ConfigDataTlbEntries",
  "RASDepth": "CVA6ConfigRASDepth",
  "BTBEntries": "CVA6ConfigBTBEntries",
  "BHTEntries": "CVA6ConfigBHTEntries",
  "NrPMPEntries": "CVA6ConfigNrPMPEntries",
  "PerfCounterEn": "CVA6ConfigPerfCounterEn",
  "DcacheType": "CVA6ConfigDcacheType",
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

  # Read file
  alllines = []
  with open("core/include/" + Args['default_config'] + "_config_pkg.sv", "r") as in_f:
    alllines = in_f.readlines()
  
  # Apply cmdline args to override individual localparam values.
  for name, value in Args.items():
    if name not in ['default_config', 'isa', 'xlen'] and value is not None:
      param = MapArgsToParameter[name]
      print("setting", name, "to", value)
      for i, line in enumerate(alllines):
        alllines[i] = re.sub(r"^(\s*localparam\s+"+param+r"\s*=\s*)(.*)(;\s*)$", r"\g<1>"+str(value)+r"\g<3>", line)

  # Build Config and warn about localparams which have no matching cmdline option associated with them.
  for line in alllines:
    linematch = re.match(r"^(\s*localparam\s+CVA6Config(?P<param>\w*)\s*=\s*)(?P<value>.*)(;\s*)$", line)
    if linematch:
      param = 'CVA6Config'+linematch.group('param')
      value = linematch.group('value')
      if linematch:
        try:
          arg = MapParametersToArgs[param]
          if value == "CVA6ConfigXlen":
              Config[arg] = Config['xlen']
          elif value == "WB":
              Config[arg] = 0
          elif value == "WT":
              Config[arg] = 1
          else:
              Config[arg] = int(value)
        except KeyError:
          print(f"WARNING: CVA6 configuration parameter '{param}' not supported yet via cmdline args,",
                "\n\t consider extending script 'config_pkg_generator.py'!")

  # Write new file
  with open("core/include/"+gen+"_config_pkg.sv", "w") as out_f:
    out_f.writelines(alllines)

  print("[Generating configuration Done]")
  return [ISA, MABI, gen, Config] # return ISA, MABI, gen (for testharness), Config for cva6.py in core-v-verif


if __name__ == "__main__":
  generate_config(sys.argv[1:])
