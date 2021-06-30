#!/usr/bin/env python3
# Copyright 2019 ETH Zurich and University of Bologna.
# SPDX-License-Identifier: Apache-2.0
import argparse
from enum import Enum
import math

MAX_DEVICES = 1023

# Function to check
# Log base 2
def Log2(x):
    return (math.log10(x) / 
            math.log10(2));
def clog2(x):
  return math.ceil(math.log(x, 2))
  
# Function to check
# if x is power of 2
def isPowerOfTwo(n):
    return (math.ceil(Log2(n)) == math.floor(Log2(n)));
#
# Generate PLIC address map
#
if __name__ == "__main__":
  # Parse the command line arguments.
  parser = argparse.ArgumentParser()
  parser.add_argument("-t", "--nr_targets", metavar="NrTargets", help="number of targets (default 2)", default=2)
  parser.add_argument("-s", "--nr_sources", metavar="NrSources", help="number of sources (default 30)", default=255)
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

  assert nr_target <= MAX_DEVICES, "Maximum allowed targets are {}".format(MAX_DEVICES)
  assert isPowerOfTwo(nr_src_eff) , "Allowed nr_source such that nr_source+1 is a power of 2"
  
  priorityBase = plic_base + 0x0
  enableBase = plic_base + 0x2000
  hartBase = plic_base + 0x200000 
  access_width=32
  
  prio="prio"
  ie="ie"
  ip="ip"
  threshold="threshold"
  cc="cc"
  
  output = "// Do not edit - auto-generated\n"
  output += "module plic_regs (\n"
  output += "  input logic [{}:0][{}:0] {}_i,\n".format(nr_src_eff-1, priority_width-1, prio)
  output += "  output logic [{}:0][{}:0] {}_o,\n".format(nr_src_eff-1, priority_width-1, prio)
  output += "  output logic [{}:0] {}_we_o,\n".format(nr_src_eff-1, prio)
  output += "  output logic [{}:0] {}_re_o,\n".format(nr_src_eff-1, prio)
  output += "  input logic [{}:0][{}:0] {}_i,\n".format(0, nr_src_eff-1, ip)
  output += "  output logic [{}:0] {}_re_o,\n".format(0, ip)
  output += "  input logic [{}:0][{}:0] {}_i,\n".format(nr_target-1, nr_src_eff-1, ie)
  output += "  output logic [{}:0][{}:0] {}_o,\n".format(nr_target-1, nr_src_eff-1, ie)
  output += "  output logic [{}:0] {}_we_o,\n".format(nr_target-1, ie)
  output += "  output logic [{}:0] {}_re_o,\n".format(nr_target-1, ie)
  output += "  input logic [{}:0][{}:0] {}_i,\n".format(nr_target-1, priority_width-1, threshold)
  output += "  output logic [{}:0][{}:0] {}_o,\n".format(nr_target-1, priority_width-1, threshold)
  output += "  output logic [{}:0] {}_we_o,\n".format(nr_target-1, threshold)
  output += "  output logic [{}:0] {}_re_o,\n".format(nr_target-1, threshold)
  output += "  input logic [{}:0][{}:0] {}_i,\n".format(nr_target-1, source_width-1, cc)
  output += "  output logic [{}:0][{}:0] {}_o,\n".format(nr_target-1, source_width-1, cc)
  output += "  output logic [{}:0] {}_we_o,\n".format(nr_target-1, cc)
  output += "  output logic [{}:0] {}_re_o,\n".format(nr_target-1, cc)
  output += "  // Bus Interface\n"
  output += "  input  reg_intf::reg_intf_req_a32_d32 req_i,\n"
  output += "  output reg_intf::reg_intf_resp_d32    resp_o\n"
  output += ");\n"
  output += "always_comb begin\n"
  output += "  resp_o.ready = 1'b1;\n"
  output += "  resp_o.rdata = '0;\n"
  output += "  resp_o.error = '0;\n"
  output += "  prio_o = '0;\n"
  output += "  prio_we_o = '0;\n"
  output += "  prio_re_o = '0;\n"
  output += "  ie_o = '0;\n"
  output += "  ie_we_o = '0;\n"
  output += "  ie_re_o = '0;\n"
  output += "  ip_re_o = '0;\n"
  output += "  threshold_o = '0;\n"
  output += "  threshold_we_o = '0;\n"
  output += "  threshold_re_o = '0;\n"
  output += "  cc_o = '0;\n"
  output += "  cc_we_o = '0;\n"
  output += "  cc_re_o = '0;\n"
  output += "  if (req_i.valid) begin\n"
  output += "    // WRITE\n"
  output += "    if (req_i.write) begin\n"
  output += "      unique case(req_i.addr)\n" 

  output += "      // SOURCES PRIORITY\n"
  for i in range(nr_src_eff):
    output += "        {}'h{}: begin\n".format(access_width, hex(priorityBase+i*4)[2:])
    output += "          {}_o[{}][{}:0] = req_i.wdata[{}:0];\n".format(prio, i, priority_width - 1, priority_width - 1)
    output += "          {}_we_o[{}] = 1'b1;\n".format(prio, i)
    output += "        end\n"

  output += "      // INTERRUPT ENABLES \n"

  for i in range(nr_target):
    for j in range(math.floor(nr_src_eff/access_width)):
      output += "        {}'h{}: begin\n".format(access_width, hex(enableBase+i*0x80+j*4)[2:])
      output += "          {}_o[{}][{}:{}] = req_i.wdata[{}:0];\n".format(ie, i, access_width*(j+1) - 1, access_width*j, access_width - 1)
      output += "          {}_we_o[{}] = 1'b1;\n".format(ie, i)
      output += "        end\n"

  output += "      // THRESHOLDS \n"

  for i in range(nr_target):
    output += "        {}'h{}: begin\n".format(access_width, hex(hartBase+i*0x1000)[2:])
    output += "          {}_o[{}][{}:0] = req_i.wdata[{}:0];\n".format(threshold, i, priority_width -1, priority_width - 1)
    output += "          {}_we_o[{}] = 1'b1;\n".format(threshold, i)
    output += "        end\n"

  output += "      // CLAIM COMPLETE \n"

  for i in range(nr_target):
    output += "        {}'h{}: begin\n".format(access_width, hex(hartBase+i*0x1000+4)[2:])
    output += "          {}_o[{}][{}:0] = req_i.wdata[{}:0];\n".format(cc, i, source_width -1, source_width - 1)
    output += "          {}_we_o[{}] = 1'b1;\n".format(cc, i)
    output += "        end\n"
    
  output += "        default: resp_o.error = 1'b1;\n"
  output += "      endcase\n"
  output += "    end else begin\n"
  output += "    // READ\n"
  output += "      unique case(req_i.addr)\n"

  output += "      // SOURCES PRIORITY\n"
  for i in range(nr_src_eff):
    output += "        {}'h{}: begin\n".format(access_width, hex(priorityBase+i*4)[2:])
    output += "          resp_o.rdata[{}:0] = {}_i[{}][{}:0];\n".format( priority_width - 1, prio, i, priority_width - 1)
    output += "          {}_re_o[{}] = 1'b1;\n".format(prio, i)
    output += "        end\n"

  output += "      // INTERRUPT PENDINGS\n"
  for j in range(math.floor(nr_src_eff/access_width)):
    output += "        {}'h{}: begin\n".format(access_width, hex(plic_base+0x1000+j*4)[2:])
    output += "          resp_o.rdata[{}:0] = {}_i[{}][{}:{}];\n".format( access_width - 1, ip, 0, access_width*(j+1) - 1, access_width*j)
    output += "          {}_re_o[{}] = 1'b1;\n".format(ip, 0)
    output += "        end\n"

  output += "      // INTERRUPT ENABLES\n"
  
  for i in range(nr_target):
    for j in range(math.floor(nr_src_eff/access_width)):
      output += "        {}'h{}: begin\n".format(access_width, hex(enableBase+i*0x80+j*4)[2:])
      output += "          resp_o.rdata[{}:0] = {}_i[{}][{}:{}];\n".format( access_width - 1, ie, i, access_width*(j+1) - 1, access_width*j)
      output += "          {}_re_o[{}] = 1'b1;\n".format(ie, i)
      output += "        end\n"

  output += "      // THRESHOLD\n"

  for i in range(nr_target):
    output += "        {}'h{}: begin\n".format(access_width, hex(hartBase+i*0x1000)[2:])
    output += "          resp_o.rdata[{}:0] = {}_i[{}][{}:0];\n".format( priority_width - 1, threshold, i, priority_width- 1)
    output += "          {}_re_o[{}] = 1'b1;\n".format(threshold, i)
    output += "        end\n"

  output += "      // CLAIM COMPLETE \n"

  for i in range(nr_target):
    output += "        {}'h{}: begin\n".format(access_width, hex(hartBase+i*0x1000+4)[2:])
    output += "          resp_o.rdata[{}:0] = {}_i[{}][{}:0];\n".format( source_width  - 1, cc, i, source_width - 1)
    output += "          {}_re_o[{}] = 1'b1;\n".format(cc, i)
    output += "        end\n"

  output += "        default: resp_o.error = 1'b1;\n"
  output += "      endcase\n"
  output += "    end\n"
  output += "  end\n"
  output += "end\n"
  output += "endmodule\n"

  print(output)
  
