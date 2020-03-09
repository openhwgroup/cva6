#!/usr/bin/env python3
# Copyright 2019 ETH Zurich and University of Bologna.
# SPDX-License-Identifier: Apache-2.0
import argparse
from enum import Enum
from math import ceil, log

MAX_DEVICES = 1023

def clog2(x):
  return ceil(log(x, 2))

class Access(Enum):
  RO = 1
  RW = 2

class AddrMapEntry(object):

  """Represents an Entry in an Address Map"""
  def __init__(self, addr, name, description, access, width):
    super(AddrMapEntry, self).__init__()
    self.addr = addr
    self.description = description
    self.access = access
    self.width = width
    self.name = name

  def __str__(self):
    return '{} | {} | {} | {}'.format(hex(self.addr), self.width, self.access, self.description)

  def get_list_elem(self):
    return [hex(self.addr), self.width, self.access, self.description]

class AddrMap:
  def __init__(self, name, description, access_width=32):
    self.access_width = access_width
    self.name = name
    self.description = description
    self.addrmap = []
    self.ports = []

  def addEntries(self, num, addr, name, description, access, width):
    # register port
    self.ports.append((name, num, width, access))
    for i in range(0, num):
      effect_addr = addr(i)
      # we need to split the entry into multiple aligned entries as otherwise we would
      # violate the access_width constraints
      if (width / self.access_width) > 1.0:
        for i in range(0, int(ceil(width / self.access_width))):
          if (width - self.access_width * i < self.access_width):
            self.addrmap.append(AddrMapEntry(effect_addr + int(self.access_width/8) * i,  name, description.format(i), access, width - self.access_width * i))
          else:
            self.addrmap.append(AddrMapEntry(effect_addr + int(self.access_width/8) * i,  name, description.format(i), access, self.access_width))
      else:
        self.addrmap.append(AddrMapEntry(effect_addr, name, description.format(i), access, width))

  def addEntry(self, addr, name, description, access, width):
    self.addEntries(1, addr, name, description, access, width)

  """Dump Verilog"""
  def emit_verilog(self):
    output = "// Do not edit - auto-generated\n"
    output += "module {} (\n".format(self.name)
    for i in self.ports:
      # self.ports.append((name, num, width, access))
      if i[3] == Access.RO:
        output += "  input logic [{}:0][{}:0] {}_i,\n".format(i[1]-1, i[2]-1, i[0])
        output += "  output logic [{}:0] {}_re_o,\n".format(i[1]-1, i[0])
      elif i[3] == Access.RW:
        output += "  input logic [{}:0][{}:0] {}_i,\n".format(i[1]-1, i[2]-1, i[0])
        output += "  output logic [{}:0][{}:0] {}_o,\n".format(i[1]-1, i[2]-1, i[0])
        output += "  output logic [{}:0] {}_we_o,\n".format(i[1]-1, i[0])
        output += "  output logic [{}:0] {}_re_o,\n".format(i[1]-1, i[0])
    output += "  // Bus Interface\n"
    output += "  input  reg_intf::reg_intf_req_a32_d32 req_i,\n"
    output += "  output reg_intf::reg_intf_resp_d32    resp_o\n"
    output += ");\n"
    output += "always_comb begin\n"
    output += "  resp_o.ready = 1'b1;\n"
    output += "  resp_o.rdata = '0;\n"
    output += "  resp_o.error = '0;\n"
    for i in self.ports:
      if i[3] != Access.RO:
        output += "  {}_o = '0;\n".format(i[0])
        output += "  {}_we_o = '0;\n".format(i[0])
        output += "  {}_re_o = '0;\n".format(i[0])
    output += "  if (req_i.valid) begin\n"
    output += "    if (req_i.write) begin\n"
    output += "      unique case(req_i.addr)\n"
    j = 0
    last_name = ""
    for i in self.addrmap:
      if i.access != Access.RO:
        if last_name != i.name:
          j = 0
        output += "        {}'h{}: begin\n".format(self.access_width, hex(i.addr)[2:])
        output += "          {}_o[{}][{}:0] = req_i.wdata[{}:0];\n".format(i.name, j, i.width - 1, i.width - 1)
        output += "          {}_we_o[{}] = 1'b1;\n".format(i.name, j)
        output += "        end\n"
        j += 1
        last_name = i.name
    output += "        default: resp_o.error = 1'b1;\n"
    output += "      endcase\n"
    output += "    end else begin\n"
    output += "      unique case(req_i.addr)\n"
    j = 0
    last_name = ""
    for i in self.addrmap:
      if last_name != i.name:
        j = 0
      output += "        {}'h{}: begin\n".format(self.access_width, hex(i.addr)[2:])
      output += "          resp_o.rdata[{}:0] = {}_i[{}][{}:0];\n".format(i.width - 1, i.name, j, i.width - 1)
      output += "          {}_re_o[{}] = 1'b1;\n".format(i.name, j)
      output += "        end\n"
      j += 1
      last_name = i.name
    output += "        default: resp_o.error = 1'b1;\n"
    output += "      endcase\n"
    output += "    end\n"
    output += "  end\n"
    output += "end\n"
    output += "endmodule\n"
    return output

#
# Generate PLIC address map
#
if __name__ == "__main__":
  # Parse the command line arguments.
  parser = argparse.ArgumentParser()
  parser.add_argument("-t", "--nr_targets", metavar="NrTargets", help="number of targets (default 2)", default=2)
  parser.add_argument("-s", "--nr_sources", metavar="NrSources", help="number of sources (default 30)", default=30)
  parser.add_argument("-p", "--max_priority", metavar="MaxPriority", help="maximum number of priority (default 7)", default=7)
  args = parser.parse_args()

  plic_base = 0xC000000

  if args.nr_targets:
    nr_target = int(args.nr_targets)

  if args.nr_sources:
    nr_src = int(args.nr_sources)

  if args.max_priority:
    max_prio = int(args.max_priority)

  priority_width = clog2(max_prio + 1)
  # interrupt source 0 is reserved, so add another source
  nr_src_eff = nr_src + 1
  source_width = clog2(nr_src_eff)
  addrmap = AddrMap("plic_regs", "PLIC Address Map")

  assert nr_src <= 31, "Not more than 31 interrupt sources are supported at the moment"
  assert nr_target <= MAX_DEVICES, "Maximum allowed targets are {}".format(MAX_DEVICES)

  priorityBase = plic_base + 0x0
  enableBase = plic_base + 0x2000
  hartBase = plic_base + 0x200000

  def pendingAddr(i):
    return plic_base + 0x1000

  def enableOffset(i):
   return i * int(((MAX_DEVICES+7)/8))

  def hartOffset(i):
    return i * 0x1000

  def priorityAddr(i):
    return priorityBase + i * 4

  def enableAddr(i):
    return enableOffset(i) + enableBase

  def hartAddr(i):
    return hartOffset(i) + hartBase

  def hartCC(i):
    return hartAddr(i) + 4

  # add priority fields
  addrmap.addEntries(nr_src_eff, priorityAddr,  "prio", "source {} priority", Access.RW, priority_width)
  # pending array
  addrmap.addEntry(pendingAddr,  "ip", "pending array", Access.RO, nr_src_eff)
  # # generate per target interrupt enables
  addrmap.addEntries(nr_target,  enableAddr, "ie", "Target {} interrupt enable", Access.RW, nr_src_eff)
  # # generate claim/complete registers + thresholds
  addrmap.addEntries(nr_target, hartAddr,  "threshold", "Hart {}  priority threshold", Access.RW, priority_width)
  addrmap.addEntries(nr_target, hartCC,  "cc", "Hart {} claim/complete", Access.RW, source_width)

  print(addrmap.emit_verilog())
