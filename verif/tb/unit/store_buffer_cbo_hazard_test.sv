// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

module store_buffer_cbo_hazard_test;

  function automatic config_pkg::cva6_cfg_t test_config();
    config_pkg::cva6_cfg_t cfg;
    cfg = build_config_pkg::build_config(cva6_config_pkg::cva6_cfg);
    return cfg;
  endfunction

  localparam config_pkg::cva6_cfg_t Cfg = test_config();

  typedef logic [7:0] cbo_t;

  typedef struct packed {
    logic [Cfg.DCACHE_INDEX_WIDTH-1:0] address_index;
    logic [Cfg.DCACHE_TAG_WIDTH-1:0] address_tag;
    logic [Cfg.XLEN-1:0] data_wdata;
    logic [Cfg.DCACHE_USER_WIDTH-1:0] data_wuser;
    logic data_req;
    logic data_we;
    logic [(Cfg.XLEN/8)-1:0] data_be;
    logic [1:0] data_size;
    logic [Cfg.DcacheIdWidth-1:0] data_id;
    logic kill_req;
    logic tag_valid;
    cbo_t cbo_op;
  } dcache_req_i_t;

  typedef struct packed {
    logic data_gnt;
    logic data_rvalid;
    logic [Cfg.DcacheIdWidth-1:0] data_rid;
    logic [Cfg.XLEN-1:0] data_rdata;
    logic [Cfg.DCACHE_USER_WIDTH-1:0] data_ruser;
    logic data_error;
  } dcache_req_o_t;

  localparam logic [Cfg.PLEN-1:0] BASE_ADDR = 'h1000;

  // The selected CBO-enabled target has a 16-byte D-cache block.
  localparam logic [11:0] SAME_ADDRESS = 12'h000;
  localparam logic [11:0] SAME_BLOCK_OTHER_WORD = 12'h008;
  localparam logic [11:0] NEXT_BLOCK = 12'h010;

  logic clk = 1'b0;
  logic rst_n = 1'b0;

  logic flush = 1'b0;
  logic stall_st_pending = 1'b0;
  logic no_st_pending;
  logic store_buffer_empty;

  logic [11:0] page_offset = '0;
  logic page_offset_matches;

  logic commit = 1'b0;
  logic commit_ready;
  logic ready;

  logic valid = 1'b0;
  logic valid_without_flush = 1'b0;

  logic [Cfg.PLEN-1:0] paddr = '0;
  logic [Cfg.PLEN-1:0] rvfi_mem_paddr;
  logic [Cfg.XLEN-1:0] data = '0;
  logic [(Cfg.XLEN/8)-1:0] be = '0;
  logic [1:0] data_size = '0;
  cbo_t cbo_op = ariane_pkg::CBO_NONE;

  dcache_req_o_t req_port_i = '0;
  dcache_req_i_t req_port_o;

  always #1 clk = !clk;

  store_buffer #(
      .CVA6Cfg(Cfg),
      .dcache_req_i_t(dcache_req_i_t),
      .dcache_req_o_t(dcache_req_o_t),
      .cbo_t(cbo_t)
  ) dut (
      .clk_i(clk),
      .rst_ni(rst_n),
      .flush_i(flush),
      .stall_st_pending_i(stall_st_pending),
      .no_st_pending_o(no_st_pending),
      .store_buffer_empty_o(store_buffer_empty),
      .page_offset_i(page_offset),
      .page_offset_matches_o(page_offset_matches),
      .commit_i(commit),
      .commit_ready_o(commit_ready),
      .ready_o(ready),
      .valid_i(valid),
      .valid_without_flush_i(valid_without_flush),
      .paddr_i(paddr),
      .rvfi_mem_paddr_o(rvfi_mem_paddr),
      .data_i(data),
      .be_i(be),
      .data_size_i(data_size),
      .cbo_op_i(cbo_op),
      .req_port_i(req_port_i),
      .req_port_o(req_port_o)
  );

  task automatic reset_dut();
    rst_n = 1'b0;

    flush = 1'b0;
    stall_st_pending = 1'b0;
    page_offset = '0;
    commit = 1'b0;
    valid = 1'b0;
    valid_without_flush = 1'b0;
    paddr = '0;
    data = '0;
    be = '0;
    data_size = '0;
    cbo_op = ariane_pkg::CBO_NONE;
    req_port_i = '0;

    repeat (2) @(posedge clk);
    #1;
    rst_n = 1'b1;

    @(posedge clk);
    #1;
  endtask

  task automatic check_match(input logic [11:0] offset, input logic expected,
                             input string description);
    page_offset = offset;
    #1;

    if (page_offset_matches !== expected) begin
      $fatal(1, "%s: expected page_offset_matches=%0b, got %0b", description, expected,
             page_offset_matches);
    end
  endtask

  task automatic check_expected_offsets(input logic cbo, input string description);
    check_match(SAME_ADDRESS, 1'b1, $sformatf("%s, same address", description));

    check_match(SAME_BLOCK_OTHER_WORD, cbo, $sformatf(
                "%s, different word in same block", description));

    check_match(NEXT_BLOCK, 1'b0, $sformatf("%s, next cache block", description));
  endtask

  task automatic test_current_entry(input cbo_t operation, input logic is_cbo,
                                    input string description);
    reset_dut();

    paddr = BASE_ADDR;
    cbo_op = operation;
    valid_without_flush = 1'b1;

    check_expected_offsets(is_cbo, description);

    valid_without_flush = 1'b0;
  endtask

  task automatic push_speculative_entry(input cbo_t operation);
    @(negedge clk);

    paddr  = BASE_ADDR;
    cbo_op = operation;
    valid  = 1'b1;

    @(posedge clk);
    #1;

    valid = 1'b0;
  endtask

  task automatic test_speculative_entry(input cbo_t operation, input logic is_cbo,
                                        input string description);
    reset_dut();

    push_speculative_entry(operation);

    check_expected_offsets(is_cbo, description);
  endtask

  task automatic test_commit_entry(input cbo_t operation, input logic is_cbo,
                                   input string description);
    reset_dut();

    // Keep the committed operation in the store buffer while checking the
    // hazard signal.
    stall_st_pending = 1'b1;

    push_speculative_entry(operation);

    commit = 1'b1;

    @(posedge clk);
    #1;

    commit = 1'b0;

    check_expected_offsets(is_cbo, description);
  endtask

  initial begin
    if (Cfg.DCACHE_LINE_WIDTH != 128) begin
      $fatal(1, "Regression expects a 128-bit/16-byte D-cache line, got %0d bits",
             Cfg.DCACHE_LINE_WIDTH);
    end

    if (Cfg.DCACHE_OFFSET_WIDTH != 4) begin
      $fatal(1, "Regression expects DCACHE_OFFSET_WIDTH=4, got %0d", Cfg.DCACHE_OFFSET_WIDTH);
    end

    // Ordinary stores must retain the existing 8-byte hazard granularity.
    test_current_entry(ariane_pkg::CBO_NONE, 1'b0, "ordinary store/current entry");

    test_speculative_entry(ariane_pkg::CBO_NONE, 1'b0, "ordinary store/speculative queue");

    test_commit_entry(ariane_pkg::CBO_NONE, 1'b0, "ordinary store/commit queue");

    // CBO.INVAL must block every younger load to the same cache block.
    test_current_entry(ariane_pkg::CBO_INVAL, 1'b1, "CBO.INVAL/current entry");

    test_speculative_entry(ariane_pkg::CBO_INVAL, 1'b1, "CBO.INVAL/speculative queue");

    test_commit_entry(ariane_pkg::CBO_INVAL, 1'b1, "CBO.INVAL/commit queue");

    // CLEAN and FLUSH have the same cache-block ordering requirement.
    test_current_entry(ariane_pkg::CBO_CLEAN, 1'b1, "CBO.CLEAN/current entry");

    test_speculative_entry(ariane_pkg::CBO_CLEAN, 1'b1, "CBO.CLEAN/speculative queue");

    test_commit_entry(ariane_pkg::CBO_CLEAN, 1'b1, "CBO.CLEAN/commit queue");

    test_current_entry(ariane_pkg::CBO_FLUSH, 1'b1, "CBO.FLUSH/current entry");

    test_speculative_entry(ariane_pkg::CBO_FLUSH, 1'b1, "CBO.FLUSH/speculative queue");

    test_commit_entry(ariane_pkg::CBO_FLUSH, 1'b1, "CBO.FLUSH/commit queue");

    $display("PASS: store-buffer CBO load hazard regression");
    $finish;
  end

endmodule
