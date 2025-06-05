// Simplified memory for WT_NEW cache
module wt_new_dcache_mem
  import ariane_pkg::*;
  import wt_cache_pkg::*;
  import wt_new_cache_pkg::*;
#(
  parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
  parameter int unsigned NUM_DUAL_SETS = wt_new_cache_pkg::NUM_DUAL_SETS
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
  output logic                        b_hit_o
);

  localparam int unsigned NUM_SETS = CVA6Cfg.DCACHE_NUM_WORDS;
  localparam int unsigned ASSOC    = CVA6Cfg.DCACHE_SET_ASSOC;

  // Split memory into regular and dual-addressable sets
  localparam int unsigned NUM_REG_SETS = NUM_SETS - NUM_DUAL_SETS;

  // Tag and data arrays
  logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0] tag_mem[NUM_SETS-1:0][ASSOC-1:0];
  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] data_mem[NUM_SETS-1:0][ASSOC-1:0];
  logic [ASSOC-1:0]                     valid_mem[NUM_SETS-1:0];

  // Flush dual sets on controller switch
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int s = 0; s < NUM_DUAL_SETS; s++) begin
        valid_mem[NUM_REG_SETS+s] <= '0;
      end
    end else if (flush_dual_i) begin
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

  // Controller B - linear search over dual sets with miss handling
  always_ff @(posedge clk_i) begin
    b_hit_o   <= 1'b0;
    b_rdata_o <= '0;
    if (b_req_i) begin
      logic found;
      found = 1'b0;
      for (int s = 0; s < NUM_DUAL_SETS; s++) begin
        int idx = NUM_REG_SETS + s;
        if (valid_mem[idx][0] && tag_mem[idx][0] == b_addr_i[CVA6Cfg.DCACHE_TAG_WIDTH-1:0]) begin
          found = 1'b1;
          b_hit_o   <= 1'b1;
          if (b_we_i)
            data_mem[idx][0] <= b_wdata_i;
          else
            b_rdata_o <= data_mem[idx][0];
        end
      end
      // For cache misses on reads, provide dummy data to prevent hang
      // For writes, install the data in the first available dual set
      if (!found) begin
        if (b_we_i) begin
          // Write miss - install in first dual set (simplified allocation)
          int install_idx = NUM_REG_SETS;
          data_mem[install_idx][0] <= b_wdata_i;
          tag_mem[install_idx][0]  <= b_addr_i[CVA6Cfg.DCACHE_TAG_WIDTH-1:0];
          valid_mem[install_idx][0] <= 1'b1;
          b_hit_o <= 1'b1; // Treat write miss as hit after installation
        end else begin
          // Read miss - provide dummy data
          b_rdata_o <= {CVA6Cfg.DCACHE_LINE_WIDTH{1'b0}}; // Return zeros
          b_hit_o <= 1'b0; // Signal miss for memory subsystem
        end
      end
    end
  end
endmodule
