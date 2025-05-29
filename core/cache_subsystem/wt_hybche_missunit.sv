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
// Description: Miss handling unit for hybrid cache implementation
//
// Modified for hybrid mode implementation with privilege-based switching

import ariane_pkg::*;
import wt_cache_pkg::*;
import wt_hybrid_cache_pkg::*;

module wt_hybche_missunit #(
  parameter config_pkg::cva6_user_cfg_t CVA6Cfg     = '0,
  parameter logic [DCACHE_SET_ASSOC-1:0]SET_MASK    = '1,
  parameter logic                       HYBRID_MODE = 1'b1, // Enable hybrid mode
  parameter wt_hybrid_cache_pkg::force_mode_e FORCE_MODE   = wt_hybrid_cache_pkg::FORCE_MODE_DYNAMIC,
  parameter wt_hybrid_cache_pkg::replacement_policy_e REPL_POLICY = wt_hybrid_cache_pkg::REPL_POLICY_RETAIN,
  parameter type axi_req_t = logic,
  parameter type axi_resp_t = logic
) (
  input  logic                           clk_i,
  input  logic                           rst_ni,
  
  // Operational mode
  input  logic                           use_set_assoc_mode_i, // Current operational mode
  input  logic                           mode_change_i,        // Mode change detected
  
  // Cache Controller Interface
  input  logic                           cache_en_i,         // Cache enabled
  input  logic                           flush_i,            // Flush request
  output logic                           flush_ack_o,        // Flush acknowledged
  input  logic                           miss_req_i,         // Miss request
  output logic                           miss_ack_o,         // Miss acknowledged
  input  logic                           miss_nc_i,          // Non-cacheable miss
  input  logic [riscv::PLEN-1:0]         miss_addr_i,        // Miss address
  output logic                           miss_busy_o,        // Miss unit busy
  
  // Mode change handling
  input  logic                           mode_flush_req_i,   // Mode change flush request
  output logic                           mode_flush_ack_o,   // Mode change flush acknowledged
  
  // AXI interface
  output axi_req_t                       axi_req_o,          // AXI request
  input  axi_resp_t                      axi_resp_i,         // AXI response
  
  // Memory interface
  output logic                           mem_req_o,          // Memory request
  output logic [riscv::PLEN-1:0]         mem_addr_o,         // Memory address
  output logic                           mem_we_o,           // Memory write enable
  output logic [DCACHE_SET_ASSOC-1:0]    mem_way_o,          // Memory way select
  output logic                           mem_busy_o          // Memory interface busy
);

  // Miss handling FSM states
  typedef enum logic [2:0] {
    IDLE,
    MODE_FLUSH,
    DRAIN_WB,
    FETCH,
    STORE
  } miss_state_e;
  
  miss_state_e state_d, state_q;
  
  // Miss tracking registers
  logic [riscv::PLEN-1:0] miss_addr_q;
  logic                   miss_nc_q;
  logic                   busy_q;
  
  // AXI transaction tracking
  logic                   axi_rd_req, axi_rd_gnt;
  logic                   axi_wr_req, axi_wr_gnt;
  logic                   axi_rd_valid;
  logic [DCACHE_LINE_WIDTH-1:0] axi_rd_data;
  
  // Mode change handling signals
  logic                   in_mode_transition;
  logic [DCACHE_SET_ASSOC-1:0] flush_ways;
  logic [DCACHE_INDEX_WIDTH-1:0] flush_index;
  logic                   flush_done;
  
  // Set in_mode_transition flag during mode transitions
  assign in_mode_transition = mode_change_i && HYBRID_MODE && 
                             (REPL_POLICY == wt_hybrid_cache_pkg::REPL_POLICY_RETAIN);
  
  // Simplified AXI interface logic for this example
  // In a real implementation, this would handle the detailed AXI protocol
  assign axi_rd_gnt = axi_resp_i.ar_ready && axi_req_o.ar_valid;
  assign axi_wr_gnt = axi_resp_i.aw_ready && axi_req_o.aw_valid;
  assign axi_rd_valid = axi_resp_i.r_valid && axi_resp_i.r.last;
  assign axi_rd_data = axi_resp_i.r.data;
  
  // Miss FSM
  always_comb begin
    // Default values
    state_d = state_q;
    miss_busy_o = busy_q;
    miss_ack_o = 1'b0;
    flush_ack_o = 1'b0;
    mode_flush_ack_o = 1'b0;
    
    mem_req_o = 1'b0;
    mem_addr_o = miss_addr_q;
    mem_we_o = 1'b0;
    mem_way_o = '0;
    mem_busy_o = 1'b0;
    
    axi_rd_req = 1'b0;
    axi_wr_req = 1'b0;
    
    case (state_q)
      IDLE: begin
        // Not busy in idle state
        miss_busy_o = 1'b0;
        
        // Handle mode flush request with RETAIN policy
        if (mode_flush_req_i && HYBRID_MODE && 
            (REPL_POLICY == wt_hybrid_cache_pkg::REPL_POLICY_RETAIN)) begin
          state_d = MODE_FLUSH;
          miss_busy_o = 1'b1;
        end
        // Handle regular miss
        else if (miss_req_i && cache_en_i) begin
          state_d = FETCH;
          miss_busy_o = 1'b1;
          miss_ack_o = 1'b1;
        end
        // Handle flush request
        else if (flush_i) begin
          state_d = DRAIN_WB;
          miss_busy_o = 1'b1;
        end
      end
      
      MODE_FLUSH: begin
        // In mode transition with RETAIN policy
        // Selective flush based on mode transition
        miss_busy_o = 1'b1;
        mem_busy_o = 1'b1;
        
        if (use_set_assoc_mode_i) begin
          // Switching TO set associative FROM fully associative
          // Reorganize cache entries based on index bits
          mem_req_o = 1'b1;
          mem_we_o = 1'b1;
          
          // Acknowledge mode flush when done
          if (flush_done) begin
            mode_flush_ack_o = 1'b1;
            state_d = IDLE;
          end
        end else begin
          // Switching TO fully associative FROM set associative
          // Update lookup table with current cache contents
          mem_req_o = 1'b1;
          
          // Acknowledge mode flush when done
          if (flush_done) begin
            mode_flush_ack_o = 1'b1;
            state_d = IDLE;
          end
        end
      end
      
      DRAIN_WB: begin
        // Draining write buffer before flush
        miss_busy_o = 1'b1;
        
        // When write buffer is empty, acknowledge flush
        flush_ack_o = 1'b1;
        state_d = IDLE;
      end
      
      FETCH: begin
        // Fetch missing cache line
        miss_busy_o = 1'b1;
        
        if (!miss_nc_q) begin
          // Cacheable miss - fetch line from memory
          axi_rd_req = 1'b1;
          
          if (axi_rd_valid) begin
            // Line received, store it
            state_d = STORE;
          end
        end else begin
          // Non-cacheable miss - direct memory access
          axi_rd_req = 1'b1;
          
          if (axi_rd_valid) begin
            // Data received, return to idle
            state_d = IDLE;
          end
        end
      end
      
      STORE: begin
        // Store fetched line into cache
        miss_busy_o = 1'b1;
        mem_req_o = 1'b1;
        mem_we_o = 1'b1;
        
        // Way selection depends on mode
        if (use_set_assoc_mode_i) begin
          // Set associative mode - use LRU or random replacement
          // (Actual way selection logic would be implemented in mem module)
        end else begin
          // Fully associative mode - find an empty slot or use replacement policy
          // (Actual way selection logic would be implemented in mem module)
        end
        
        // Return to idle when done
        state_d = IDLE;
      end
      
      default: begin
        // Invalid state - return to IDLE
        state_d = IDLE;
      end
    endcase
  end
  
  // State register
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= IDLE;
      miss_addr_q <= '0;
      miss_nc_q <= 1'b0;
      busy_q <= 1'b0;
    end else begin
      state_q <= state_d;
      busy_q <= miss_busy_o;
      
      if (miss_req_i && state_q == IDLE) begin
        miss_addr_q <= miss_addr_i;
        miss_nc_q <= miss_nc_i;
      end
    end
  end

endmodule
