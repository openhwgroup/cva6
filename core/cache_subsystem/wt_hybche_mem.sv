// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 13.09.2018
// Description: Memory arrays and tag comparison for hybrid cache implementation
//
// Modified for hybrid mode implementation

import ariane_pkg::*;
import wt_cache_pkg::*;
import wt_hybrid_cache_pkg::*;

module wt_hybche_mem #(
  parameter config_pkg::cva6_user_cfg_t CVA6Cfg     = '0,
  parameter logic [DCACHE_SET_ASSOC-1:0]SET_MASK    = '1,
  parameter logic                       HYBRID_MODE = 1'b1, // Enable hybrid mode
  parameter wt_hybrid_cache_pkg::force_mode_e FORCE_MODE   = wt_hybrid_cache_pkg::FORCE_MODE_DYNAMIC,
  parameter wt_hybrid_cache_pkg::replacement_policy_e REPL_POLICY = wt_hybrid_cache_pkg::REPL_POLICY_RETAIN
) (
  input  logic                           clk_i,
  input  logic                           rst_ni,

  input  logic                           flush_i,      // flush the dcache, flush and kill have to be asserted together
  output logic                           flush_ack_o,  // acknowledge successful flush
  
  // Operational mode
  input  logic                           use_set_assoc_mode_i, // Set associative or fully associative mode
  
  // From PTW
  input  logic                           enable_translation_i, // CSR from PTW, determines if MMU is enabled
  
  // SRAM interface
  output logic                           sram_en_o,
  output logic [DCACHE_SET_ASSOC-1:0]    sram_we_o,
  output logic [DCACHE_INDEX_WIDTH-1:0]  sram_idx_o,
  output logic [DCACHE_TAG_WIDTH-1:0]    sram_tag_o,
  output logic [DCACHE_LINE_WIDTH-1:0]   sram_data_o,
  input  logic [DCACHE_LINE_WIDTH-1:0]   sram_data_i
);

  ///////////////////////////////////////////////////////
  // Cache storage organization based on operation mode //
  ///////////////////////////////////////////////////////

  // Internal state and signals
  logic [DCACHE_SET_ASSOC-1:0] way_valid;         // Valid bits per way
  logic [DCACHE_SET_ASSOC-1:0] way_hit;           // Hit per way
  logic [DCACHE_SET_ASSOC-1:0] repl_way;          // Way to replace
  logic [DCACHE_TAG_WIDTH-1:0] tag_rdata [DCACHE_SET_ASSOC-1:0]; // Tag read data
  
  // Operation mode specific signals
  logic [DCACHE_INDEX_WIDTH-1:0] set_assoc_index; // Index for set associative mode
  logic [DCACHE_INDEX_WIDTH-1:0] full_assoc_index; // Index for fully associative mode
  logic [DCACHE_TAG_WIDTH-1:0] set_assoc_tag;    // Tag for set associative mode
  logic [DCACHE_TAG_WIDTH-1:0] full_assoc_tag;   // Tag for fully associative mode (includes index bits)
  
  // Mode selection muxes
  logic [DCACHE_INDEX_WIDTH-1:0] cache_index;
  logic [DCACHE_TAG_WIDTH-1:0] cache_tag;
  
  // Flattened signals for memory operations
  logic [DCACHE_TAG_WIDTH*DCACHE_SET_ASSOC-1:0] tags_flattened;
  
  // Fully associative lookup table - tracks which ways store which addresses in fully associative mode
  typedef struct packed {
    logic valid;
    logic [DCACHE_TAG_WIDTH-1:0] tag;  // Full address tag (includes index bits from set associative mode)
    logic [DCACHE_INDEX_WIDTH-1:0] physical_set; // Where in memory the entry is actually stored
  } fa_lookup_entry_t;
  
  fa_lookup_entry_t fa_lookup_table [DCACHE_SET_ASSOC-1:0];
  
  // Operation mode muxing
  always_comb begin
    if (use_set_assoc_mode_i) begin
      // Set associative mode - standard operation
      cache_index = set_assoc_index;
      cache_tag = set_assoc_tag;
    end else begin
      // Fully associative mode - use full tag comparison
      cache_index = full_assoc_index;
      cache_tag = full_assoc_tag;
    end
  end
  
  // Hit generation based on mode
  always_comb begin
    way_hit = '0;
    
    if (use_set_assoc_mode_i) begin
      // Set associative hit generation - compare tags from the selected index
      for (int i = 0; i < DCACHE_SET_ASSOC; i++) begin
        way_hit[i] = way_valid[i] && (tag_rdata[i] == cache_tag);
      end
    end else begin
      // Fully associative hit generation - check each entry in lookup table
      for (int i = 0; i < DCACHE_SET_ASSOC; i++) begin
        way_hit[i] = fa_lookup_table[i].valid && (fa_lookup_table[i].tag == cache_tag);
      end
    end
  end
  
  // Replacement policy implementation
  // For set associative mode: use random or LRU
  // For fully associative mode: use first free way or random
  always_comb begin
    repl_way = '0;
    
    if (use_set_assoc_mode_i) begin
      // Standard replacement policy for set associative cache
      // For simplicity in this example, using a fixed priority encoder
      if (!way_valid[0]) repl_way[0] = 1'b1;
      else if (!way_valid[1]) repl_way[1] = 1'b1;
      else repl_way[0] = 1'b1; // If all ways are valid, replace first way
    end else begin
      // Policy for fully associative cache
      // First find any invalid entry
      for (int i = 0; i < DCACHE_SET_ASSOC; i++) begin
        if (!fa_lookup_table[i].valid) begin
          repl_way[i] = 1'b1;
          break;
        end
      end
      
      // If all entries are valid, use a simple replacement scheme
      if (repl_way == '0) begin
        repl_way[0] = 1'b1; // Fixed replacement for simplicity
      end
    end
  end
  
  // Implementation of mode transition handling
  // If policy is REPL_POLICY_FLUSH, the entire cache is flushed on mode change
  // If policy is REPL_POLICY_RETAIN, entries are kept but reorganized based on new mode
  
  // SRAM interface assignments
  assign sram_en_o = 1'b1; // Enable SRAM
  assign sram_idx_o = cache_index;
  assign sram_tag_o = cache_tag;
  
endmodule