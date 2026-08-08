// Copyright 2026 Keerthivasan
//
// Licensed under the Solderpad Hardware Licence, Version 2.0.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

module tb_zcmt_decoder;

  function automatic config_pkg::cva6_cfg_t make_cfg();
    config_pkg::cva6_cfg_t cfg;

    cfg = config_pkg::cva6_cfg_empty;

    cfg.XLEN = 32;
    cfg.VLEN = 32;
    cfg.IS_XLEN32 = 1'b1;
    cfg.IS_XLEN64 = 1'b0;

    make_cfg = cfg;
  endfunction

  localparam config_pkg::cva6_cfg_t CVA6Cfg = make_cfg();

  typedef struct packed {
    logic [25:0] base;
    logic [5:0]  mode;
  } jvt_t;

  typedef struct packed {
    logic [9:0]  address_index;
    logic [21:0] address_tag;
    logic [31:0] data_wdata;
    logic        data_wuser;
    logic        data_req;
    logic        data_we;
    logic [3:0]  data_be;
    logic [1:0]  data_size;
    logic        data_id;
    logic        kill_req;
    logic        tag_valid;
  } dcache_req_i_t;

  typedef struct packed {
    logic        data_rvalid;
    logic [31:0] data_rdata;
  } dcache_req_o_t;

  logic clk_i;
  logic rst_ni;

  logic [31:0] instr_i;
  logic [31:0] pc_i;

  logic is_zcmt_instr_i;
  logic illegal_instr_i;
  logic is_compressed_i;

  jvt_t jvt_i;

  dcache_req_o_t req_port_i;
  dcache_req_i_t req_port_o;

  logic [31:0] instr_o;
  logic illegal_instr_o;
  logic is_compressed_o;
  logic fetch_stall_o;
  logic [31:0] jump_address_o;

  zcmt_decoder #(
      .CVA6Cfg(CVA6Cfg),
      .dcache_req_i_t(dcache_req_i_t),
      .dcache_req_o_t(dcache_req_o_t),
      .jvt_t(jvt_t),
      .branchpredict_sbe_t(logic)
  ) dut (
      .clk_i,
      .rst_ni,
      .instr_i,
      .pc_i,
      .is_zcmt_instr_i,
      .illegal_instr_i,
      .is_compressed_i,
      .jvt_i,
      .req_port_i,
      .instr_o,
      .illegal_instr_o,
      .is_compressed_o,
      .fetch_stall_o,
      .req_port_o,
      .jump_address_o
  );

  initial clk_i = 1'b0;
  always #5 clk_i = ~clk_i;

  task automatic check_index(input int unsigned index);
    logic [15:0] encoding;
    logic [31:0] actual_address;
    logic [31:0] expected_address;

    begin
      // Force the decoder FSM back to IDLE for each independent case.
      rst_ni = 1'b0;
      is_zcmt_instr_i = 1'b0;

      @(posedge clk_i);
      #1;

      rst_ni = 1'b1;

      @(negedge clk_i);

      // cm.jt/cm.jalt encoding:
      // index occupies instruction bits [9:2].
      encoding = 16'ha002 | {6'b0, index[7:0], 2'b00};

      instr_i = {16'h0000, encoding};
      pc_i = 32'h8000_0000;

      // JVT base = 0x80100000.
      jvt_i.base = 26'h2004000;
      jvt_i.mode = 6'b0;

      req_port_i = '0;

      illegal_instr_i = 1'b0;
      is_compressed_i = 1'b1;
      is_zcmt_instr_i = 1'b1;

      #1;

      actual_address   = {req_port_o.address_tag, req_port_o.address_index};

      expected_address = 32'h8010_0000 + (index << 2);

      $display("index=%0d encoding=%h actual=%h expected=%h", index, encoding, actual_address,
               expected_address);

      if (!req_port_o.data_req) begin
        $fatal(1, "index %0d: Zcmt table request was not asserted", index);
      end

      if (actual_address !== expected_address) begin
        $fatal(1, "index %0d: wrong table address: actual=%h expected=%h", index, actual_address,
               expected_address);
      end

      is_zcmt_instr_i = 1'b0;
    end
  endtask

  initial begin
    rst_ni = 1'b0;
    instr_i = '0;
    pc_i = '0;
    is_zcmt_instr_i = 1'b0;
    illegal_instr_i = 1'b0;
    is_compressed_i = 1'b0;
    jvt_i = '0;
    req_port_i = '0;

    // Values below 64 prove the existing behavior remains unchanged.
    check_index(0);
    check_index(31);
    check_index(32);
    check_index(63);

    // 64 is the first value affected by #3442.
    check_index(64);

    // Additional upper-range coverage.
    check_index(127);
    check_index(128);
    check_index(255);

    $display("PASS: complete eight-bit Zcmt JVT index is used");
    $finish;
  end

endmodule
