// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Paul Scheffler <paulsc@iis.ee.ethz.ch>
// Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

// Wrappers mapping HPDcache SRAMs to PULP `tc_sram`.

/// SRAM with one R/W port and no write mask
module hpdcache_sram_1rw #(
    parameter int unsigned ADDR_SIZE = 0,
    parameter int unsigned DATA_SIZE = 0,
    parameter int unsigned DEPTH = 2 ** ADDR_SIZE,
    parameter int unsigned NDATA = 1
) (
    input  logic                                clk,
    input  logic                                rst_n,
    input  logic                                cs,
    input  logic                                we,
    input  logic [ADDR_SIZE-1:0]                addr,
    input  logic [    NDATA-1:0][DATA_SIZE-1:0] wdata,
    output logic [    NDATA-1:0][DATA_SIZE-1:0] rdata
);
  localparam int unsigned FLAT_DATA_SIZE = NDATA * DATA_SIZE;
  logic [FLAT_DATA_SIZE-1:0] wdata_flat;
  logic [FLAT_DATA_SIZE-1:0] rdata_flat;
  genvar i;
  generate
    for (i = 0; i < NDATA; i++) begin
      assign wdata_flat[(i+1)*DATA_SIZE-1:i*DATA_SIZE] = wdata[i];
      assign rdata[i] = rdata_flat[(i+1)*DATA_SIZE-1:i*DATA_SIZE];
    end
  endgenerate
  tc_sram #(
      .NumWords (DEPTH),
      .DataWidth(FLAT_DATA_SIZE),
      .ByteWidth(FLAT_DATA_SIZE),
      .NumPorts (1),
      .Latency  (1)
  ) i_tc_sram (
      .clk_i  (clk),
      .rst_ni (rst_n),
      .req_i  (cs),
      .we_i   (we),
      .addr_i (addr),
      .wdata_i(wdata_flat),
      .be_i   (1'b1),
      .rdata_o(rdata_flat)
  );
endmodule

/// SRAM with one R/W port and per-byte write mask
module hpdcache_sram_wbyteenable_1rw #(
    parameter int unsigned ADDR_SIZE = 0,
    parameter int unsigned DATA_SIZE = 0,
    parameter int unsigned DEPTH = 2 ** ADDR_SIZE,
    parameter int unsigned NDATA = 1
) (
    input  logic                                  clk,
    input  logic                                  rst_n,
    input  logic                                  cs,
    input  logic                                  we,
    input  logic [ADDR_SIZE-1:0]                  addr,
    input  logic [    NDATA-1:0][  DATA_SIZE-1:0] wdata,
    input  logic [    NDATA-1:0][DATA_SIZE/8-1:0] wbyteenable,
    output logic [    NDATA-1:0][  DATA_SIZE-1:0] rdata
);
  localparam int unsigned FLAT_DATA_SIZE = NDATA * DATA_SIZE;
  logic [FLAT_DATA_SIZE    -1:0] wdata_flat;
  logic [FLAT_DATA_SIZE    -1:0] rdata_flat;
  logic [(FLAT_DATA_SIZE/8)-1:0] wbyteenable_flat;
  genvar i;
  generate
    for (i = 0; i < NDATA; i++) begin
      assign wdata_flat[(i+1)*DATA_SIZE-1:i*DATA_SIZE] = wdata[i];
      assign wbyteenable_flat[(i+1)*(DATA_SIZE/8)-1:i*(DATA_SIZE/8)] = wbyteenable[i];
      assign rdata[i] = rdata_flat[(i+1)*DATA_SIZE-1:i*DATA_SIZE];
    end
  endgenerate
  tc_sram #(
      .NumWords (DEPTH),
      .DataWidth(FLAT_DATA_SIZE),
      .ByteWidth(8),
      .NumPorts (1),
      .Latency  (1)
  ) i_tc_sram (
      .clk_i  (clk),
      .rst_ni (rst_n),
      .req_i  (cs),
      .we_i   (we),
      .addr_i (addr),
      .wdata_i(wdata_flat),
      .be_i   (wbyteenable_flat),
      .rdata_o(rdata_flat)
  );
endmodule

/// SRAM with one R/W port and per-bit write mask
module hpdcache_sram_wmask_1rw #(
    parameter int unsigned ADDR_SIZE = 0,
    parameter int unsigned DATA_SIZE = 0,
    parameter int unsigned DEPTH = 2 ** ADDR_SIZE,
    parameter int unsigned NDATA = 1
) (
    input  logic                                clk,
    input  logic                                rst_n,
    input  logic                                cs,
    input  logic                                we,
    input  logic [ADDR_SIZE-1:0]                addr,
    input  logic [    NDATA-1:0][DATA_SIZE-1:0] wdata,
    input  logic [    NDATA-1:0][DATA_SIZE-1:0] wmask,
    output logic [    NDATA-1:0][DATA_SIZE-1:0] rdata
);
  localparam int unsigned FLAT_DATA_SIZE = NDATA * DATA_SIZE;
  logic [FLAT_DATA_SIZE-1:0] wdata_flat;
  logic [FLAT_DATA_SIZE-1:0] rdata_flat;
  logic [FLAT_DATA_SIZE-1:0] wmask_flat;
  genvar i;
  generate
    for (i = 0; i < NDATA; i++) begin
      assign wdata_flat[(i+1)*DATA_SIZE-1:i*DATA_SIZE] = wdata[i];
      assign wmask_flat[(i+1)*DATA_SIZE-1:i*DATA_SIZE] = wmask[i];
      assign rdata[i] = rdata_flat[(i+1)*DATA_SIZE-1:i*DATA_SIZE];
    end
  endgenerate
  tc_sram #(
      .NumWords (DEPTH),
      .DataWidth(FLAT_DATA_SIZE),
      .ByteWidth(1),
      .NumPorts (1),
      .Latency  (1)
  ) i_tc_sram (
      .clk_i  (clk),
      .rst_ni (rst_n),
      .req_i  (cs),
      .we_i   (we),
      .addr_i (addr),
      .wdata_i(wdata_flat),
      .be_i   (wmask_flat),
      .rdata_o(rdata_flat)
  );
endmodule
