// Copyright 2022 Thales Research and Technology
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses
//
// Inferable, Asynchronous Single-Port RAM
//
// This module is designed to work with both Xilinx and Microchip FPGA tools by following the respective
// guidelines:
// - Xilinx UG901 Vivado Design Suite User Guide: Synthesis
// - Inferring Microchip PolarFire RAM Blocks
//
// Intel FPGA (Altera) doesn't seem to support asynchronous RAM
//
// Original Author: Sébastien Jacq - sjthales on github.com

 
module AsyncSpRam
#(
  parameter ADDR_WIDTH = 10,
  parameter DATA_WIDTH = 32
)(
  input  logic                    clk_i,
  input  logic                    we_i,
  input  logic [ADDR_WIDTH-1:0]   read_address_i,
  input  logic [ADDR_WIDTH-1:0]   write_address_i,
  input  logic [DATA_WIDTH-1:0]   wdata_i,
  output logic [DATA_WIDTH-1:0]   rdata_o
);

  logic [DATA_WIDTH-1:0] mem [(2**ADDR_WIDTH)-1:0]= '{default:0};

  always @(posedge clk_i)
    if (we_i)
      mem[write_address_i] <= wdata_i;

  assign rdata_o = mem[read_address_i];

endmodule 
