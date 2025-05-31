// Write-through cache with dual-addressable sets (WT_NEW)
module wt_new_cache_subsystem
  import ariane_pkg::*;
  import wt_cache_pkg::*;
  import wt_new_cache_pkg::*;
#(
  parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
  parameter int unsigned NUM_DUAL_SETS = wt_new_cache_pkg::NUM_DUAL_SETS
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  ariane_pkg::priv_lvl_t priv_lvl_i,

  // Controller A interface
  input  logic                 a_req_i,
  input  logic [CVA6Cfg.DCACHE_INDEX_WIDTH-1:0] a_index_i,
  input  logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0]   a_tag_i,
  input  logic                 a_we_i,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  a_wdata_i,
  output logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  a_rdata_o,

  // Controller B interface
  input  logic                 b_req_i,
  input  logic [CVA6Cfg.PLEN-1:0] b_addr_i,
  input  logic                 b_we_i,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] b_wdata_i,
  output logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] b_rdata_o,
  output logic                 b_hit_o
);

  // Track privilege level to detect mode switches
  ariane_pkg::priv_lvl_t priv_lvl_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) priv_lvl_q <= ariane_pkg::PRIV_LVL_M;
    else priv_lvl_q <= priv_lvl_i;
  end

  // Switch occurs when privilege level changes
  logic switch_ctrl;
  assign switch_ctrl = (priv_lvl_q != priv_lvl_i);

  // Instantiate memory with two controller ports
  wt_new_dcache_mem #(
    .CVA6Cfg      (CVA6Cfg),
    .NUM_DUAL_SETS(NUM_DUAL_SETS)
  ) i_mem (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .flush_dual_i (switch_ctrl),

    // Controller A
    .a_req_i    (a_req_i),
    .a_index_i  (a_index_i),
    .a_tag_i    (a_tag_i),
    .a_we_i     (a_we_i),
    .a_wdata_i  (a_wdata_i),
    .a_rdata_o  (a_rdata_o),

    // Controller B
    .b_req_i    (b_req_i),
    .b_addr_i   (b_addr_i),
    .b_we_i     (b_we_i),
    .b_wdata_i  (b_wdata_i),
    .b_rdata_o  (b_rdata_o),
    .b_hit_o    (b_hit_o)
  );
endmodule
