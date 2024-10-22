// Copyright 2025 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Yannick Casamatta - Thales
// Date: 22/10/2024

module hpdcache_sram_1rw
#(
    parameter int unsigned ADDR_SIZE = 0,
    parameter int unsigned DATA_SIZE = 0,
    parameter int unsigned DEPTH = 2**ADDR_SIZE
)
(
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  cs,
    input  logic                  we,
    input  logic [ADDR_SIZE-1:0]  addr,
    input  logic [DATA_SIZE-1:0]  wdata,
    output logic [DATA_SIZE-1:0]  rdata
);

    SyncSpRam #(
      .ADDR_WIDTH(ADDR_SIZE),
      .DATA_DEPTH(DEPTH), // usually 2**ADDR_WIDTH, but can be lower
      .DATA_WIDTH(DATA_SIZE),
      .OUT_REGS  (0),
      .SIM_INIT  (1)     // for simulation only, will not be synthesized
                                   // 0: no init, 1: zero init, 2: random init
                                   // note: on verilator, 2 is not supported. define the VERILATOR macro to work around.
    )SyncSpRam_i(
      .Clk_CI   (clk),
      .Rst_RBI  (rst_n),
      .CSel_SI  (cs),
      .WrEn_SI  (we),
      .Addr_DI  (addr),
      .WrData_DI(wdata),
      .RdData_DO(rdata)
    );


endmodule : hpdcache_sram_1rw
