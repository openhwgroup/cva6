// Copyright 2022 Thales Research and Technology
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Sébastien Jacq

module tc_sram_wrapper #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width
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

  SyncSpRamBeNx64 #(
    .ADDR_WIDTH(AddrWidth),
    .DATA_DEPTH(NumWords),
    .OUT_REGS (0),
    // this initializes the memory with 0es. adjust to taste...
    // 0: no init, 1: zero init, 2: random init, 3: deadbeef init
    .SIM_INIT (1)
  ) i_ram (
    .Clk_CI    ( clk_i      ),
    .Rst_RBI   ( rst_ni     ),
    .CSel_SI   ( req_i[0]   ),
    .WrEn_SI   ( we_i[0]    ),
    .BEn_SI    ( be_i[0]    ),
    .WrData_DI ( wdata_i[0] ),
    .Addr_DI   ( addr_i[0]  ),
    .RdData_DO ( rdata_o[0] )
  );




endmodule
