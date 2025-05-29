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
// Description: Write buffer for hybrid cache implementation
//
// Modified for hybrid mode support

import ariane_pkg::*;
import wt_cache_pkg::*;
import wt_hybrid_cache_pkg::*;

module wt_hybche_wbuffer #(
  parameter config_pkg::cva6_cfg_t CVA6Cfg     = '0,
  parameter int unsigned                DEPTH       = 8,
  parameter logic                       HYBRID_MODE = 1'b1, // Enable hybrid mode
  parameter wt_hybrid_cache_pkg::force_mode_e FORCE_MODE   = wt_hybrid_cache_pkg::FORCE_MODE_DYNAMIC,
  parameter wt_hybrid_cache_pkg::replacement_policy_e REPL_POLICY = wt_hybrid_cache_pkg::REPL_POLICY_RETAIN,
  parameter type axi_req_t = logic,
  parameter type axi_resp_t = logic
) (
  input  logic                           clk_i,
  input  logic                           rst_ni,
  
  // Core request interface
  input  logic                           valid_i,
  input  logic [riscv::PLEN-1:0]         addr_i,
  input  logic                           we_i,
  input  logic [CVA6Cfg.XLEN/8-1:0]      be_i,
  input  logic [CVA6Cfg.XLEN-1:0]        data_i,
  output logic                           ready_o,

  // Operational mode
  input  logic                           use_set_assoc_mode_i, // Current mode
  input  logic                           mode_change_i,        // Mode change

  // Write buffer status
  output logic                           empty_o,
  input  logic                           flush_i,
  output logic                           flush_ack_o,
  
  // Invalidation interface
  input  logic                           cache_en_i,  
  input  logic                           inval_i,
  input  logic [riscv::PLEN-1:0]         inval_addr_i,
 
  // AXI interface
  output axi_req_t                       axi_req_o,
  input  axi_resp_t                      axi_resp_i,

  // Memory priority
  input  logic                           mem_priority_i  // Higher priority for memory transactions
);

  // Write buffer entry data structure
  typedef struct packed {
    logic [riscv::PLEN-1:0]      addr;
    logic [CVA6Cfg.XLEN-1:0]     data;
    logic [CVA6Cfg.XLEN/8-1:0]   be;
    logic                        set_assoc_mode; // Mode used when entry was inserted
  } wbuffer_entry_t;
  
  // Write buffer state
  wbuffer_entry_t [DEPTH-1:0] buffer_q;
  logic [DEPTH-1:0]           valid_q;
  logic [$clog2(DEPTH)-1:0]   next_free;
  logic [$clog2(DEPTH)-1:0]   next_to_write;
  
  // AXI transaction tracking
  logic                       axi_wr_req, axi_wr_gnt;
  logic                       axi_wr_valid;
  
  // Buffer status
  logic                       buffer_full;
  logic                       buffer_empty;
  
  // Calculate buffer status
  assign buffer_empty = (valid_q == '0);
  assign buffer_full = (valid_q == '1);
  assign empty_o = buffer_empty;
  
  // Find first free entry (priority encoder)
  always_comb begin
    next_free = '0;
    for (int i = 0; i < DEPTH; i++) begin
      if (!valid_q[i]) begin
        next_free = i[$clog2(DEPTH)-1:0];
        break;
      end
    end
  end
  
  // Find next entry to write out (FIFO order)
  always_comb begin
    next_to_write = '0;
    for (int i = 0; i < DEPTH; i++) begin
      if (valid_q[i]) begin
        next_to_write = i[$clog2(DEPTH)-1:0];
        break;
      end
    end
  end
  
  // Simplified AXI interface logic
  assign axi_wr_gnt = axi_resp_i.aw_ready && axi_req_o.aw_valid;
  assign axi_wr_valid = axi_resp_i.b_valid;
  
  // Main FSM for write buffer management
  enum logic [1:0] {
    IDLE,
    DRAIN,
    FLUSH
  } state_d, state_q;
  
  // Ready signal generation
  assign ready_o = (!buffer_full || (state_q == DRAIN && axi_wr_gnt)) && state_q != FLUSH;
  
  always_comb begin
    // Default values
    state_d = state_q;
    flush_ack_o = 1'b0;
    axi_wr_req = 1'b0;
    
    case (state_q)
      IDLE: begin
        // Normal operation - accept writes, drain buffer when possible
        if (!buffer_empty && (mem_priority_i || !valid_i)) begin
          // Start draining write buffer when memory has priority or no new request
          axi_wr_req = 1'b1;
          if (axi_wr_gnt) begin
            state_d = DRAIN;
          end
        end
        
        // Handle flush request
        if (flush_i) begin
          state_d = FLUSH;
        end
      end
      
      DRAIN: begin
        // Draining the buffer
        if (buffer_empty) begin
          // Buffer is empty, return to idle
          state_d = IDLE;
        end else begin
          // Continue draining
          axi_wr_req = 1'b1;
          
          // Wait for transaction to complete
          if (axi_wr_valid) begin
            if (buffer_empty) begin
              state_d = IDLE;
            end
          end
        end
        
        // Handle flush request
        if (flush_i) begin
          state_d = FLUSH;
        end
      end
      
      FLUSH: begin
        // Flushing the buffer
        if (buffer_empty) begin
          // Buffer is empty, acknowledge flush and return to idle
          flush_ack_o = 1'b1;
          state_d = IDLE;
        end else begin
          // Drain buffer to complete flush
          axi_wr_req = 1'b1;
          
          if (axi_wr_gnt) begin
            state_d = DRAIN;
          end
        end
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
  
  // Write buffer valid bit management
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= '0;
      buffer_q <= '0;
    end else begin
      // Add new entry to buffer
      if (valid_i && ready_o) begin
        valid_q[next_free] <= 1'b1;
        buffer_q[next_free].addr <= addr_i;
        buffer_q[next_free].data <= data_i;
        buffer_q[next_free].be <= be_i;
        buffer_q[next_free].set_assoc_mode <= use_set_assoc_mode_i;
      end
      
      // Remove entry when transaction complete
      if (axi_wr_valid && state_q == DRAIN) begin
        valid_q[next_to_write] <= 1'b0;
      end
      
      // Invalidate matching addresses
      if (cache_en_i && inval_i) begin
        for (int i = 0; i < DEPTH; i++) begin
          if (valid_q[i] && (buffer_q[i].addr[riscv::PLEN-1:3] == inval_addr_i[riscv::PLEN-1:3])) begin
            valid_q[i] <= 1'b0;
          end
        end
      end
    end
  end
  
  // AXI write request generation
  always_comb begin
    // Default values
    axi_req_o = '0;
    
    if (axi_wr_req && !buffer_empty) begin
      // Get write data from the buffer entry being drained
      axi_req_o.aw_valid = 1'b1;
      axi_req_o.aw.addr = buffer_q[next_to_write].addr;
      axi_req_o.aw.size = $clog2(CVA6Cfg.XLEN/8);
      
      axi_req_o.w_valid = 1'b1;
      axi_req_o.w.data = buffer_q[next_to_write].data;
      axi_req_o.w.strb = buffer_q[next_to_write].be;
      axi_req_o.w.last = 1'b1;
      
      axi_req_o.b_ready = 1'b1;
    end
  end

endmodule
