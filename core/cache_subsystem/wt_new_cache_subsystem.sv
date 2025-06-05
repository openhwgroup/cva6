// Write-through cache with dual-addressable sets (WT_NEW)
module wt_new_cache_subsystem
  import ariane_pkg::*;
  import wt_cache_pkg::*;
  import wt_new_cache_pkg::*;
#(
  parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
  parameter int unsigned NUM_DUAL_SETS = wt_new_cache_pkg::NUM_DUAL_SETS,
  parameter wt_new_replacement_e REPLACEMENT_POLICY = wt_new_replacement_e'(
    REPL_ROUND_ROBIN),
  parameter wt_new_flush_policy_e FLUSH_POLICY = wt_new_flush_policy_e'(
    FLUSH_ON_SWITCH),
  parameter wt_new_b_ctrl_e B_CTRL = wt_new_b_ctrl_e'(B_CTRL_ENABLE)
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic [1:0]           priv_lvl_i,

  // Unified cache request interface
  input  logic                 req_i,
  input  logic [CVA6Cfg.PLEN-1:0] addr_i,
  input  logic                 we_i,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  wdata_i,
  output logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  rdata_o,
  output logic                 hit_o,

  // Monitoring counters
  output logic [31:0]          hit_count_o,
  output logic [31:0]          miss_count_o,
  output logic [31:0]          switch_count_o
);

  // Track privilege level to detect mode switches
  logic [1:0] priv_lvl_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) priv_lvl_q <= 2'b11;  // PRIV_LVL_M equivalent
    else priv_lvl_q <= priv_lvl_i;
  end

  // Switch occurs when privilege level changes
  logic switch_ctrl;
  assign switch_ctrl = (priv_lvl_q != priv_lvl_i);

  // Count privilege level switches
  logic [31:0] switch_counter;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      switch_counter <= '0;
    end else if (switch_ctrl) begin
      switch_counter <= switch_counter + 1;
    end
  end

  // Address decode for controller A
  localparam int unsigned OFFSET_WIDTH = CVA6Cfg.DCACHE_OFFSET_WIDTH;
  localparam int unsigned INDEX_WIDTH  = CVA6Cfg.DCACHE_INDEX_WIDTH;

  logic [INDEX_WIDTH-1:0]              a_index;
  logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0] a_tag;

  assign a_index = addr_i[OFFSET_WIDTH + INDEX_WIDTH - 1: OFFSET_WIDTH];
  assign a_tag   = addr_i[CVA6Cfg.PLEN-1: OFFSET_WIDTH + INDEX_WIDTH];

  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] a_rdata;
  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] b_rdata;
  logic                                b_hit;

  // Instantiate memory with two controller ports
  wt_new_dcache_mem #(
    .CVA6Cfg      (CVA6Cfg),
    .NUM_DUAL_SETS(NUM_DUAL_SETS),
    .REPLACEMENT_POLICY(REPLACEMENT_POLICY),
    .FLUSH_POLICY (FLUSH_POLICY),
    .B_CTRL       (B_CTRL)
  ) i_mem (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .flush_dual_i (switch_ctrl),

    // Controller A
    .a_req_i    (priv_lvl_i == 2'b11 ? req_i : 1'b0),  // Machine mode
    .a_index_i  (a_index),
    .a_tag_i    (a_tag),
    .a_we_i     (we_i),
    .a_wdata_i  (wdata_i),
    .a_rdata_o  (a_rdata),

    // Controller B
    .b_req_i    (priv_lvl_i != 2'b11 ? req_i : 1'b0),  // Non-machine mode
    .b_addr_i   (addr_i),
    .b_we_i     (we_i),
    .b_wdata_i  (wdata_i),
    .b_rdata_o  (b_rdata),
    .b_hit_o    (b_hit),
    .hit_count_o(hit_count_o),
    .miss_count_o(miss_count_o)
  );

  assign rdata_o = (priv_lvl_i == 2'b11) ? a_rdata : b_rdata;  // Machine mode uses controller A
  assign hit_o   = (priv_lvl_i == 2'b11) ? 1'b1 : b_hit;  // Machine mode always hits
  assign switch_count_o = switch_counter;
endmodule
