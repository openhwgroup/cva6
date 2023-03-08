// Copyright 2022 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON - Thales

module tc_sram_wrapper_256_64_00000008_00000001_00000001_none_0 #(
  parameter int unsigned NumWords     = 32'd256, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd64,  // Data signal width
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte
  parameter int unsigned NumPorts     = 32'd1,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter              SimInit      = "none",   // Simulation initialization
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth, // ceil_div
  parameter type         addr_t    = logic [AddrWidth-1:0],
  parameter type         data_t    = logic [DataWidth-1:0],
  parameter type         be_t      = logic [BeWidth-1:0]
) (
  input  logic                 clk_i,      // Clock
  input  logic                 rst_ni,     // Asynchronous reset active low
  // input ports
  input  logic  [NumPorts-1:0] req_i,      // request
  input  logic  [NumPorts-1:0] we_i,       // write enable
  input  addr_t [NumPorts-1:0] addr_i,     // request address
  input  data_t [NumPorts-1:0] wdata_i,    // write data
  input  be_t   [NumPorts-1:0] be_i,       // write byte enable
  // output ports
  output data_t [NumPorts-1:0] rdata_o     // read data
);

// synthesis translate_off

  tc_sram #(
    .NumWords(NumWords),
    .DataWidth(DataWidth),
    .ByteWidth(ByteWidth),
    .NumPorts(NumPorts),
    .Latency(Latency),
    .SimInit(SimInit),
    .PrintSimCfg(PrintSimCfg)
  ) i_tc_sram (
      .clk_i    ( clk_i   ),
      .rst_ni   ( rst_ni  ),
      .req_i    ( req_i   ),
      .we_i     ( we_i    ),
      .be_i     ( be_i    ),
      .wdata_i  ( wdata_i ),
      .addr_i   ( addr_i  ),
      .rdata_o  ( rdata_o )
    );

// synthesis translate_on

endmodule
