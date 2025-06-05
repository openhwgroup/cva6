// Simplified memory for WT_NEW cache
module wt_new_dcache_mem
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
  input  logic clk_i,
  input  logic rst_ni,

  // Flush dual sets when switching controllers
  input  logic flush_dual_i,

  // Controller A interface (set associative like WT cache)
  input  logic                        a_req_i,
  input  logic [CVA6Cfg.DCACHE_INDEX_WIDTH-1:0] a_index_i,
  input  logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0]   a_tag_i,
  input  logic                        a_we_i,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  a_wdata_i,
  output logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  a_rdata_o,

  // Controller B interface (fully associative over dual sets)
  input  logic                        b_req_i,
  input  logic [CVA6Cfg.PLEN-1:0]     b_addr_i,
  input  logic                        b_we_i,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  b_wdata_i,
  output logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]  b_rdata_o,
  output logic                        b_hit_o,

  // Monitoring counters
  output logic [63:0]                 hit_count_o,
  output logic [63:0]                 miss_count_o
);

  localparam int unsigned NUM_SETS = CVA6Cfg.DCACHE_NUM_WORDS;
  localparam int unsigned ASSOC    = CVA6Cfg.DCACHE_SET_ASSOC;

  // Split memory into regular and dual-addressable sets
  localparam int unsigned NUM_REG_SETS = NUM_SETS - NUM_DUAL_SETS;

  // Tag and data arrays
  logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0] tag_mem[NUM_SETS-1:0][ASSOC-1:0];
  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] data_mem[NUM_SETS-1:0][ASSOC-1:0];
  logic [ASSOC-1:0]                     valid_mem[NUM_SETS-1:0];

  // Replacement state for dual sets
  logic [$clog2(NUM_DUAL_SETS)-1:0] repl_ptr;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      repl_ptr <= '0;
    end else if (b_req_i && !b_hit_o && B_CTRL == B_CTRL_ENABLE) begin
      case (REPLACEMENT_POLICY)
        REPL_ROUND_ROBIN: repl_ptr <= repl_ptr + 1'b1;
        REPL_RANDOM: repl_ptr <= {$random} % NUM_DUAL_SETS;
        default: repl_ptr <= repl_ptr + 1'b1;
      endcase
    end
  end

  // Statistics counters
  logic [63:0] hit_count;
  logic [63:0] miss_count;

  // Flush dual sets on controller switch
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int s = 0; s < NUM_DUAL_SETS; s++) begin
        valid_mem[NUM_REG_SETS+s] <= '0;
      end
    end else if (flush_dual_i && FLUSH_POLICY == FLUSH_ON_SWITCH) begin
      for (int s = 0; s < NUM_DUAL_SETS; s++) begin
        valid_mem[NUM_REG_SETS+s] <= '0;
      end
    end
  end

  // Controller A - simple single-cycle access
  always_ff @(posedge clk_i) begin
    if (a_req_i) begin
      if (a_we_i) begin
        data_mem[a_index_i % NUM_SETS][0] <= a_wdata_i; // simplified: way 0 only
        tag_mem[a_index_i % NUM_SETS][0]  <= a_tag_i;
        valid_mem[a_index_i % NUM_SETS][0] <= 1'b1;
      end else begin
        a_rdata_o <= data_mem[a_index_i % NUM_SETS][0];
      end
    end
  end

  // Controller B - lookup over dual sets with enhanced miss handling
  always_ff @(posedge clk_i) begin
    b_hit_o   <= 1'b0;
    b_rdata_o <= '0;
    if (b_req_i && B_CTRL == B_CTRL_ENABLE) begin
      int lookup_idx = NUM_REG_SETS;
      // Try hashed lookup first for REPL_PSEUDO_LRU
      if (REPLACEMENT_POLICY == REPL_PSEUDO_LRU) begin
        lookup_idx = NUM_REG_SETS + (b_addr_i[3:0] % NUM_DUAL_SETS);
        if (valid_mem[lookup_idx][0] &&
            tag_mem[lookup_idx][0] == b_addr_i[CVA6Cfg.DCACHE_TAG_WIDTH-1:0]) begin
          b_hit_o <= 1'b1;
          if (b_we_i) data_mem[lookup_idx][0] <= b_wdata_i;
          else        b_rdata_o <= data_mem[lookup_idx][0];
        end
      end
      // Linear search if no hash hit
      if (!b_hit_o) begin
        for (int s = 0; s < NUM_DUAL_SETS; s++) begin
          int idx = NUM_REG_SETS + s;
          if (valid_mem[idx][0] &&
              tag_mem[idx][0] == b_addr_i[CVA6Cfg.DCACHE_TAG_WIDTH-1:0]) begin
            b_hit_o <= 1'b1;
            if (b_we_i) data_mem[idx][0] <= b_wdata_i;
            else        b_rdata_o <= data_mem[idx][0];
          end
        end
      end
      // Handle cache misses with proper allocation and dummy data
      if (!b_hit_o) begin
        if (b_we_i) begin
          // Write miss - allocate using replacement policy
          int alloc_idx = NUM_REG_SETS + repl_ptr;
          tag_mem[alloc_idx][0]  <= b_addr_i[CVA6Cfg.DCACHE_TAG_WIDTH-1:0];
          data_mem[alloc_idx][0] <= b_wdata_i;
          valid_mem[alloc_idx][0] <= 1'b1;
          b_hit_o <= 1'b1; // Treat write miss as hit after installation
        end else begin
          // Read miss - provide dummy data to prevent hang
          b_rdata_o <= {CVA6Cfg.DCACHE_LINE_WIDTH{1'b0}}; // Return zeros
          // Keep b_hit_o = 1'b0 to signal miss for memory subsystem
        end
      end
    end
  end

  // Count hits and misses
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      hit_count  <= '0;
      miss_count <= '0;
    end else if (b_req_i && B_CTRL == B_CTRL_ENABLE) begin
      if (b_hit_o) hit_count <= hit_count + 1;
      else          miss_count <= miss_count + 1;
    end
  end

  assign hit_count_o  = hit_count;
  assign miss_count_o = miss_count;
endmodule
