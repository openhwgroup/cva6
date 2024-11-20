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
    parameter int unsigned DEPTH = 2**ADDR_SIZE
)
(
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic                   cs,
    input  logic                   we,
    input  logic [ADDR_SIZE-1:0]   addr,
    input  logic [DATA_SIZE-1:0]   wdata,
    input  logic [DATA_SIZE/8-1:0] wbyteenable,
    output logic [DATA_SIZE-1:0]   rdata
);

if (DATA_SIZE == 128) begin
    // Découpage des données en deux moitiés de 64 bits
    logic [DATA_SIZE/2-1:0] wdata_low, wdata_high;
    logic [DATA_SIZE/2-1:0] rdata_low, rdata_high;
    logic [7:0] be_low, be_high;
    assign wdata_low  = wdata[63:0];
    assign wdata_high = wdata[127:64];
    assign be_low  = wbyteenable[7:0];
    assign be_high = wbyteenable[15:8];

    SyncSpRamBeNx64 #(
        .ADDR_WIDTH(ADDR_SIZE),
        .DATA_DEPTH(DEPTH),
        .OUT_REGS  (0),
        .SIM_INIT  (1)
    ) SyncSpRam_0 (
        .Clk_CI   (clk),
        .Rst_RBI  (rst_n),
        .CSel_SI  (cs),
        .WrEn_SI  (we),          // Ecriture sur la banque basse
        .BEn_SI   (be_low),
        .Addr_DI  (addr),
        .WrData_DI(wdata_low),
        .RdData_DO(rdata_low)
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
        .WrEn_SI  (we),          // Ecriture sur la banque haute
        .BEn_SI   (be_high),
        .Addr_DI  (addr),
        .WrData_DI(wdata_high),
        .RdData_DO(rdata_high)
    );

    assign rdata = {rdata_high, rdata_low};

end else if (DATA_SIZE == 64) begin
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
end else if (DATA_SIZE == 32) begin
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
   $fatal(1, "DATASIZE=%d, in not supported " ,DATA_SIZE);
end


endmodule : hpdcache_sram_wbyteenable_1rw
