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
// Description: Write-through cache subsystem with hybrid mode support
// 
// Modified for hybrid mode implementation: Allows switching between
// set associative mode (faster, standard WT cache) and fully associative mode
// (better isolation with privilege-based accesses)

import ariane_pkg::*;
import wt_cache_pkg::*;
import wt_hybrid_cache_pkg::*;

module wt_hybche #(
  parameter config_pkg::cva6_cfg_t CVA6Cfg     = '0,
  parameter int unsigned                DREQ_DEPTH  = 2,
  parameter logic [CVA6Cfg.DCACHE_SET_ASSOC-1:0]SET_MASK    = '1,
  parameter logic                       HYBRID_MODE = 1'b1, // Enable hybrid mode
  parameter wt_hybrid_cache_pkg::force_mode_e FORCE_MODE   = wt_hybrid_cache_pkg::FORCE_MODE_DYNAMIC,
  parameter wt_hybrid_cache_pkg::replacement_policy_e REPL_POLICY = wt_hybrid_cache_pkg::REPL_POLICY_RETAIN,
  parameter wt_hybrid_cache_pkg::replacement_algo_e   REPL_ALGO   = wt_hybrid_cache_pkg::REPL_ALGO_RR,
  // Seed value for the hash function when operating in fully associative mode
  parameter logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0] HASH_SEED = wt_hybrid_cache_pkg::DEFAULT_HASH_SEED[CVA6Cfg.DCACHE_TAG_WIDTH-1:0],
  parameter type axi_req_t = logic,
  parameter type axi_resp_t = logic,
  parameter type dcache_req_i_t = logic,
  parameter type dcache_req_o_t = logic
) (
  input  logic                           clk_i,
  input  logic                           rst_ni,

  input  logic                           flush_i,      // flush the dcache, flush and kill have to be asserted together
  output logic                           flush_ack_o,  // acknowledge successful flush
  
  // Privilege mode input
  input  logic [1:0]                     priv_lvl_i,   // From CSR, used for hybrid mode (2'b00=U, 2'b01=S, 2'b11=M)
  
  // From PTW
  input  logic                           enable_translation_i, // CSR from PTW, determines if MMU is enabled
  
  // SRAM interface
  output logic                           sram_en_o,
  output logic [CVA6Cfg.DCACHE_SET_ASSOC-1:0]    sram_we_o,
  output logic [CVA6Cfg.DCACHE_INDEX_WIDTH-1:0]  sram_idx_o,
  output logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0]    sram_tag_o,
  output logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]   sram_data_o,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]   sram_data_i,
  
  // Cache management
  input  logic                           cache_en_i,   // from CSR
  input  logic                           cache_flush_i,// high until acknowledged
  output logic                           cache_flush_ack_o,
  
  // Core request ports
  input  dcache_req_i_t [CVA6Cfg.NrLoadPipeRegs+CVA6Cfg.NrStorePipeRegs-1:0] dcache_req_ports_i,
  output dcache_req_o_t [CVA6Cfg.NrLoadPipeRegs+CVA6Cfg.NrStorePipeRegs-1:0] dcache_req_ports_o,
  
  // AXI port
  output axi_req_t  axi_req_o,
  input  axi_resp_t axi_resp_i
);

  // Determine cache operation mode
  logic use_set_assoc_mode;
  
  // If hybrid mode is enabled, determine operational mode based on privilege level
  // Use set associative mode for machine mode (highest performance)
  // Use fully associative mode for supervisor/user mode (better isolation)
  // This can be overridden by FORCE_MODE parameter
  always_comb begin
    if (HYBRID_MODE) begin
      case(FORCE_MODE)
        wt_hybrid_cache_pkg::FORCE_MODE_DYNAMIC: begin
          // Dynamic mode - switch based on privilege level
          // M-mode (3) uses set associative, S-mode (1) and U-mode (0) use fully associative
          use_set_assoc_mode = (priv_lvl_i == 2'b11); // Machine mode
        end
        wt_hybrid_cache_pkg::FORCE_MODE_SET_ASS: begin
          // Force set associative mode (like standard WT cache)
          use_set_assoc_mode = 1'b1;
        end
        wt_hybrid_cache_pkg::FORCE_MODE_FULL_ASS: begin
          // Force fully associative mode
          use_set_assoc_mode = 1'b0;
        end
        default: begin
          // Default to set associative for undefined cases
          use_set_assoc_mode = 1'b1;
        end
      endcase
    end else begin
      // When hybrid mode is disabled, always use set associative mode
      use_set_assoc_mode = 1'b1;
    end
  end

  // Track privilege mode changes to trigger flush if needed
  logic prev_set_assoc_mode_q;
  logic mode_change;
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prev_set_assoc_mode_q <= 1'b1; // Default to set associative after reset
    end else begin
      prev_set_assoc_mode_q <= use_set_assoc_mode;
    end
  end
  
  // Detect mode change
  assign mode_change = (prev_set_assoc_mode_q != use_set_assoc_mode);
  
  // Flush control signal - flush on explicit request or on mode change when REPL_POLICY_FLUSH is used
  logic flush_cache;
  assign flush_cache = flush_i || (mode_change && (REPL_POLICY == wt_hybrid_cache_pkg::REPL_POLICY_FLUSH));

  // Internal cache components
  wt_hybche_mem #(
    .CVA6Cfg       ( CVA6Cfg            ),
    .SET_MASK      ( SET_MASK           ),
    .HYBRID_MODE   ( HYBRID_MODE        ),
    .FORCE_MODE    ( FORCE_MODE         ),
    .REPL_POLICY   ( REPL_POLICY        ),
    .REPL_ALGO     ( REPL_ALGO          ),
    .HASH_SEED     ( HASH_SEED          )
  ) i_wt_hybche_mem (
    .clk_i,
    .rst_ni,
    .use_set_assoc_mode_i ( use_set_assoc_mode ),
    .flush_i              ( flush_cache        ),
    .flush_ack_o,
    .enable_translation_i,
    .sram_en_o,
    .sram_we_o,
    .sram_idx_o,
    .sram_tag_o,
    .sram_data_o,
    .sram_data_i
  );
  
  // Wire up the rest of the components (controllers, miss handling, etc.)
  // These would be implemented in their respective modules
  
endmodule
