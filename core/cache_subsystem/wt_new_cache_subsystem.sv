// Enhanced write-through cache with dual-addressable sets (WT_NEW)
module wt_new_cache_subsystem
  import ariane_pkg::*;
  import wt_cache_pkg::*;
  import wt_new_cache_pkg::*;
  import riscv::*;
#(
  parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
  parameter int unsigned NUM_DUAL_SETS = wt_new_cache_pkg::NUM_DUAL_SETS,
  parameter wt_new_replacement_e REPLACEMENT_POLICY = wt_new_replacement_e'(
    REPL_ROUND_ROBIN),
  parameter wt_new_flush_policy_e FLUSH_POLICY = wt_new_flush_policy_e'(
    FLUSH_ON_SWITCH),
  parameter wt_new_b_ctrl_e B_CTRL = wt_new_b_ctrl_e'(B_CTRL_ENABLE),
  parameter type axi_req_t = logic,
  parameter type axi_rsp_t = logic,
  // NEW: Configurable privilege mode control - CONFIGURED FOR REAL MODE
  parameter bit ENABLE_PRIV_MODIFIER = 1'b0,  // 0=real mode (simulation control), 1=test mode  
  parameter int unsigned PRIV_SWITCH_PERIOD = 0   // Disabled for real mode
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  priv_lvl_t            priv_lvl_i,

  // NEW: Test mode control
  input  logic                 test_mode_enable_i,  // Runtime override for test mode

  // Unified cache request interface
  input  logic                 req_i,
  input  logic [CVA6Cfg.PLEN-1:0] addr_i,
  input  logic                 we_i,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  wdata_i,
  output logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  rdata_o,
  output logic                 hit_o,

  // Memory interface for miss handling
  output axi_req_t             axi_data_req_o,
  input  axi_rsp_t             axi_data_rsp_i,

  // Monitoring counters
  output logic [63:0]          hit_count_o,
  output logic [63:0]          miss_count_o,
  output logic [63:0]          switch_count_o,
  
  // NEW: Debug outputs for privilege mode control
  output priv_lvl_t            effective_priv_lvl_o,  // Which privilege level is actually used
  output logic                 priv_mode_override_o,  // 1=test mode active, 0=real mode
  output logic [31:0]          test_cycle_counter_o   // Test mode cycle counter
);

  // NEW: Configurable privilege mode control
  priv_lvl_t effective_priv_lvl;
  logic priv_mode_override;
  logic [31:0] test_cycle_counter;
  
  // Test mode privilege modifier (100-cycle switching)
  priv_lvl_t test_mode_priv_lvl;
  logic test_mode_switch_event;
  
  generate
    if (ENABLE_PRIV_MODIFIER) begin : gen_priv_modifier
      priv_lvl_modifier #(
        .SWITCH_PERIOD(PRIV_SWITCH_PERIOD)
      ) i_priv_modifier (
        .clk_i                  (clk_i),
        .rst_ni                 (rst_ni),
        .actual_priv_lvl_i      (priv_lvl_i),
        .modified_priv_lvl_o    (test_mode_priv_lvl),
        .cycle_counter_o        (test_cycle_counter),
        .privilege_switch_event_o(test_mode_switch_event),
        .in_machine_mode_o      (),
        .in_user_mode_o         ()
      );
    end else begin : gen_no_priv_modifier
      assign test_mode_priv_lvl = priv_lvl_i;
      assign test_cycle_counter = '0;
      assign test_mode_switch_event = 1'b0;
    end
  endgenerate
  
  // Runtime selection between test mode and real mode
  always_comb begin
    if ((ENABLE_PRIV_MODIFIER && test_mode_enable_i) || 
        (ENABLE_PRIV_MODIFIER && !test_mode_enable_i && PRIV_SWITCH_PERIOD > 0)) begin
      // Test mode: Use 100-cycle artificial switching
      effective_priv_lvl = test_mode_priv_lvl;
      priv_mode_override = 1'b1;
    end else begin
      // Real mode: Use actual simulation privilege level
      effective_priv_lvl = priv_lvl_i;
      priv_mode_override = 1'b0;
    end
  end
  
  // Assign debug outputs
  assign effective_priv_lvl_o = effective_priv_lvl;
  assign priv_mode_override_o = priv_mode_override;
  assign test_cycle_counter_o = test_cycle_counter;

  // Detect privilege level switches using helper module
  logic switch_ctrl;
  logic [63:0] switch_counter;

  priv_lvl_switch_detector i_priv_switch (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .priv_lvl_i    (effective_priv_lvl),  // Use effective privilege level
    .switch_o      (switch_ctrl),
    .switch_count_o(switch_counter)
  );

  // Address decode for controller A
  localparam int unsigned OFFSET_WIDTH = CVA6Cfg.DCACHE_OFFSET_WIDTH;
  localparam int unsigned INDEX_WIDTH  = CVA6Cfg.DCACHE_INDEX_WIDTH;

  logic [INDEX_WIDTH-1:0]              a_index;
  logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0] a_tag;

  assign a_index = addr_i[OFFSET_WIDTH + INDEX_WIDTH - 1: OFFSET_WIDTH];
  assign a_tag   = addr_i[CVA6Cfg.PLEN-1: CVA6Cfg.DCACHE_OFFSET_WIDTH + CVA6Cfg.DCACHE_INDEX_WIDTH];

  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] a_rdata;
  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] b_rdata;
  logic                                a_hit;
  logic                                b_hit;

  // Instantiate enhanced memory with two controller ports
  logic flush_dual_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      flush_dual_q <= 1'b0;
    end else begin
      flush_dual_q <= switch_ctrl;
    end
  end

  wt_new_dcache_mem #(
    .CVA6Cfg      (CVA6Cfg),
    .NUM_DUAL_SETS(NUM_DUAL_SETS),
    .REPLACEMENT_POLICY(REPLACEMENT_POLICY),
    .FLUSH_POLICY (FLUSH_POLICY),
    .B_CTRL       (B_CTRL),
    .axi_req_t    (axi_req_t),
    .axi_rsp_t    (axi_rsp_t)
  ) i_mem (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .flush_dual_i (flush_dual_q),

    // Controller A
    .a_req_i    (effective_priv_lvl == PRIV_LVL_M ? req_i : 1'b0),  // Machine mode
    .a_index_i  (a_index),
    .a_tag_i    (a_tag),
    .a_we_i     (we_i),
    .a_wdata_i  (wdata_i),
    .a_rdata_o  (a_rdata),
    .a_hit_o    (a_hit),

    // Controller B
    .b_req_i    (effective_priv_lvl != PRIV_LVL_M ? req_i : 1'b0),  // Non-machine mode
    .b_addr_i   (addr_i),
    .b_we_i     (we_i),
    .b_wdata_i  (wdata_i),
    .b_rdata_o  (b_rdata),
    .b_hit_o    (b_hit),

    // Memory interface
    .axi_data_req_o (axi_data_req_o),
    .axi_data_rsp_i (axi_data_rsp_i),

    // Monitoring
    .hit_count_o(hit_count_o),
    .miss_count_o(miss_count_o)
  );

  assign rdata_o = (effective_priv_lvl == PRIV_LVL_M) ? a_rdata : b_rdata;  // Machine mode uses controller A
  assign hit_o   = (effective_priv_lvl == PRIV_LVL_M) ? a_hit : b_hit;  // Both controllers now properly report hits
  assign switch_count_o = switch_counter;
endmodule
