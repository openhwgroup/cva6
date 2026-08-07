// Copyright 2025 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Yannick Casamatta - Thales
// Date: 22/10/2024

module hpdcache_sram_wbyteenable_1rw
#(
    parameter int unsigned ADDR_SIZE = 0,
    parameter int unsigned DATA_SIZE = 0,
    parameter int unsigned DEPTH = 2**ADDR_SIZE,
    parameter int unsigned NDATA = 1
)
(
    input  logic                              clk,
    input  logic                              rst_n,
    input  logic                              cs,
    input  logic                              we,
    input  logic [ADDR_SIZE-1:0]              addr,
    input  logic [NDATA-1:0][DATA_SIZE-1:0]   wdata,
    input  logic [NDATA-1:0][DATA_SIZE/8-1:0] wbyteenable,
    output logic [NDATA-1:0][DATA_SIZE-1:0]   rdata
);

if (NDATA*DATA_SIZE == 128) begin
    // split in two 64-bits wide SRAMs
    logic [127:0] __wdata;
    logic [127:0] __rdata;
    logic [15:0]  __be;

    assign __wdata = wdata;
    assign __be    = wbyteenable;

    SyncSpRamBeNx64 #(
        .ADDR_WIDTH(ADDR_SIZE),
        .DATA_DEPTH(DEPTH),
        .OUT_REGS  (0),
        .SIM_INIT  (1)
    ) SyncSpRam_0 (
        .Clk_CI   (clk),
        .Rst_RBI  (rst_n),
        .CSel_SI  (cs),
        .WrEn_SI  (we),
        .BEn_SI   (__be[0 +: 8]), // write LSBs
        .Addr_DI  (addr),
        .WrData_DI(__wdata[0 +: 64]),
        .RdData_DO(__rdata[0 +: 64])
    );

    SyncSpRamBeNx64 #(
        .ADDR_WIDTH(ADDR_SIZE),
        .DATA_DEPTH(DEPTH),
        .OUT_REGS  (0),
        .SIM_INIT  (1)
    ) SyncSpRam_1 (
        .Clk_CI   (clk),
        .Rst_RBI  (rst_n),
        .CSel_SI  (cs),
        .WrEn_SI  (we),
        .BEn_SI   (__be[8 +: 8]), // write MSbs
        .Addr_DI  (addr),
        .WrData_DI(__wdata[64 +: 64]),
        .RdData_DO(__rdata[64 +: 64])
    );

    assign rdata = __rdata;

end else if (NDATA*DATA_SIZE == 64) begin
    SyncSpRamBeNx64 #(
      .ADDR_WIDTH(ADDR_SIZE),
      .DATA_DEPTH(DEPTH), // usually 2**ADDR_WIDTH, but can be lower
      .OUT_REGS  (0),
      .SIM_INIT  (1)     // for simulation only, will not be synthesized
                                   // 0: no init, 1: zero init, 2: random init
                                   // note: on verilator, 2 is not supported. define the VERILATOR macro to work around.
    )SyncSpRam_i(
      .Clk_CI   (clk),
      .Rst_RBI  (rst_n),
      .CSel_SI  (cs),
      .WrEn_SI  (we),
      .BEn_SI   (wbyteenable),
      .Addr_DI  (addr),
      .WrData_DI(wdata),
      .RdData_DO(rdata)
    );
end else if (NDATA*DATA_SIZE == 32) begin
    SyncSpRamBeNx32 #(
      .ADDR_WIDTH(ADDR_SIZE),
      .DATA_DEPTH(DEPTH), // usually 2**ADDR_WIDTH, but can be lower
      .OUT_REGS  (0),
      .SIM_INIT  (1)     // for simulation only, will not be synthesized
                                   // 0: no init, 1: zero init, 2: random init
                                   // note: on verilator, 2 is not supported. define the VERILATOR macro to work around.
    )SyncSpRam_i(
      .Clk_CI   (clk),
      .Rst_RBI  (rst_n),
      .CSel_SI  (cs),
      .WrEn_SI  (we),
      .BEn_SI   (wbyteenable),
      .Addr_DI  (addr),
      .WrData_DI(wdata),
      .RdData_DO(rdata)
    );

end else begin
   $fatal(1, "DATASIZE=%d, in not supported", NDATA*DATA_SIZE);
end


endmodule : hpdcache_sram_wbyteenable_1rw
