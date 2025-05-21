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
// Description: Controller for hybrid cache with privilege-based access modes
//
// Modified for hybrid mode implementation

import ariane_pkg::*;
import wt_cache_pkg::*;
import wt_hybrid_cache_pkg::*;

module wt_hybche_ctrl #(
  parameter config_pkg::cva6_user_cfg_t CVA6Cfg     = '0,
  parameter logic [DCACHE_SET_ASSOC-1:0]SET_MASK    = '1,
  parameter logic                       HYBRID_MODE = 1'b1, // Enable hybrid mode
  parameter wt_hybrid_cache_pkg::force_mode_e FORCE_MODE   = wt_hybrid_cache_pkg::FORCE_MODE_DYNAMIC,
  parameter wt_hybrid_cache_pkg::replacement_policy_e REPL_POLICY = wt_hybrid_cache_pkg::REPL_POLICY_RETAIN
) (
  input  logic                           clk_i,
  input  logic                           rst_ni,

  // Cache control signal inputs
  input  logic                           flush_i,       // flush the dcache
  output logic                           flush_ack_o,   // acknowledge successful flush
  input  logic                           cache_en_i,    // from CSR
  input  logic                           cache_flush_i, // high until acknowledged
  output logic                           cache_flush_ack_o,
  
  // Operational mode
  input  logic                           use_set_assoc_mode_i, // Set associative or fully associative mode
  input  logic                           mode_change_i,  // Privilege mode change detected
  
  // Memory interface
  input  logic                           miss_req_i,    // Miss detected, initiate memory request
  output logic                           miss_ack_o,    // Acknowledge miss handling
  input  logic                           miss_dirty_i,  // Need to writeback
  input  logic [riscv::PLEN-1:0]         miss_addr_i,   // Address to fetch
  output logic                           miss_busy_o,   // Miss handling unit busy
  
  // New mode-specific signals
  output logic                           mode_flush_req_o, // Request flush due to mode change
  input  logic                           mode_flush_ack_i, // Acknowledge mode change flush
  
  // SRAM control interface
  output logic                           sram_en_o,
  output logic [DCACHE_SET_ASSOC-1:0]    sram_we_o,
  
  // Memory stage interface - req/ack signals
  input  logic                           mem_ready_i,   // Memory stage accepts request
  output logic                           mem_valid_o,   // Memory stage request valid
  
  // Performance counters
  output logic                           trans_cnt_o,    // Number of mode transitions
  output logic                           set_hit_cnt_o,  // Hit in set associative mode
  output logic                           full_hit_cnt_o  // Hit in fully associative mode
);

  ////////////////////
  // Cache FSM      //
  ////////////////////

  // Cache controller states
  typedef enum logic [2:0] {
    IDLE,
    FLUSH,
    MODE_TRANS,
    MISS_REQ,
    MISS_WAIT,
    UPDATE
  } cache_ctrl_e;
  
  cache_ctrl_e state_d, state_q;
  
  // Transition counters
  logic [31:0] trans_cnt_q;
  logic [31:0] set_hit_cnt_q;
  logic [31:0] full_hit_cnt_q;
  
  // Control signals
  logic cache_active;
  logic handling_mode_change;
  logic execute_flush;
  
  // Cache is active when enabled and not in flush state
  assign cache_active = cache_en_i && !cache_flush_i;
  
  // Execute flush either on explicit request or when mode changes with FLUSH policy
  assign execute_flush = cache_flush_i || 
                        (mode_change_i && (REPL_POLICY == wt_hybrid_cache_pkg::REPL_POLICY_FLUSH) && HYBRID_MODE);
  
  // Transition counter - increments on every mode change
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      trans_cnt_q <= '0;
    end else if (mode_change_i && HYBRID_MODE) begin
      trans_cnt_q <= trans_cnt_q + 1;
    end
  end
  
  // Set associative hit counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      set_hit_cnt_q <= '0;
    end else if (use_set_assoc_mode_i && mem_valid_o && mem_ready_i && !miss_req_i) begin
      set_hit_cnt_q <= set_hit_cnt_q + 1;
    end
  end
  
  // Fully associative hit counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      full_hit_cnt_q <= '0;
    end else if (!use_set_assoc_mode_i && mem_valid_o && mem_ready_i && !miss_req_i) begin
      full_hit_cnt_q <= full_hit_cnt_q + 1;
    end
  end
  
  // Export counter values
  assign trans_cnt_o = (trans_cnt_q > 0);
  assign set_hit_cnt_o = (set_hit_cnt_q > 0);
  assign full_hit_cnt_o = (full_hit_cnt_q > 0);
  
  // FSM for cache control
  always_comb begin
    // Default values
    state_d = state_q;
    flush_ack_o = 1'b0;
    cache_flush_ack_o = 1'b0;
    miss_ack_o = 1'b0;
    miss_busy_o = 1'b0;
    mem_valid_o = 1'b0;
    mode_flush_req_o = 1'b0;
    sram_en_o = 1'b0;
    sram_we_o = '0;
    
    case (state_q)
      IDLE: begin
        // Memory requests can be handled
        mem_valid_o = cache_active;
        
        // Handle mode transition
        if (execute_flush) begin
          state_d = FLUSH;
        end else if (mode_change_i && HYBRID_MODE && 
                    (REPL_POLICY == wt_hybrid_cache_pkg::REPL_POLICY_RETAIN)) begin
          state_d = MODE_TRANS;
          mode_flush_req_o = 1'b1;
        end else if (miss_req_i && cache_active) begin
          state_d = MISS_REQ;
          miss_busy_o = 1'b1;
        end
      end
      
      FLUSH: begin
        // Flush the entire cache
        sram_en_o = 1'b1;
        sram_we_o = '0; // Don't write, just invalidate
        
        // Acknowledge flush when done
        flush_ack_o = 1'b1;
        cache_flush_ack_o = 1'b1;
        
        // Return to IDLE when done
        state_d = IDLE;
      end
      
      MODE_TRANS: begin
        // Handle privilege level mode transition with retention policy
        miss_busy_o = 1'b1;
        mode_flush_req_o = 1'b1;
        
        // When mode transition flush is acknowledged, move to update state
        if (mode_flush_ack_i) begin
          state_d = UPDATE;
        end
      end
      
      MISS_REQ: begin
        // Handle cache miss
        miss_busy_o = 1'b1;
        miss_ack_o = 1'b1;
        
        // Transition to wait state
        state_d = MISS_WAIT;
      end
      
      MISS_WAIT: begin
        // Wait for miss to be serviced
        miss_busy_o = 1'b1;
        
        // Transition to update once memory request is complete
        if (!miss_busy_o) begin
          state_d = UPDATE;
        end
      end
      
      UPDATE: begin
        // Update cache with new data
        sram_en_o = 1'b1;
        sram_we_o = SET_MASK;
        
        // Return to IDLE
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
    end else begin
      state_q <= state_d;
    end
  end

endmodule