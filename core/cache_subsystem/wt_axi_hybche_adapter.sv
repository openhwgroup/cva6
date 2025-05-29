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
// Description: AXI adapter for hybrid cache implementation
//
// Modified for hybrid mode implementation

import ariane_pkg::*;
import wt_cache_pkg::*;
import wt_hybrid_cache_pkg::*;

module wt_axi_hybche_adapter #(
  parameter config_pkg::cva6_cfg_t CVA6Cfg     = '0,
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
  
  // Cache controller interface
  input  logic                           req_i,
  input  logic [riscv::PLEN-1:0]         addr_i,
  input  logic                           we_i,
  input  logic [CVA6Cfg.DCACHE_SET_ASSOC-1:0]    way_i,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]   data_i,
  input  logic [CVA6Cfg.DCACHE_LINE_WIDTH/8-1:0] be_i,
  output logic                           gnt_o,
  
  output logic                           we_o,
  output logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0]   data_o,
  
  // AXI interface
  output axi_req_t                       axi_req_o,
  input  axi_resp_t                      axi_resp_i
);

  ///////////////////////////
  // AXI State and Signals //
  ///////////////////////////

  // AXI transaction state
  typedef enum logic [1:0] {
    IDLE,
    READ,
    WRITE
  } axi_state_e;
  
  axi_state_e state_d, state_q;
  
  // AXI request tracking
  logic [riscv::PLEN-1:0]      req_addr_q;
  logic                        req_we_q;
  logic [DCACHE_SET_ASSOC-1:0] req_way_q;
  logic [DCACHE_LINE_WIDTH-1:0] req_data_q;
  logic [DCACHE_LINE_WIDTH/8-1:0] req_be_q;
  
  // AXI status signals
  logic ar_sent, aw_sent, w_sent;
  logic ar_ready, aw_ready, w_ready, b_valid, r_valid;
  logic [DCACHE_LINE_WIDTH-1:0] r_data;
  logic r_last;
  
  // AXI signal assignments
  assign ar_ready = axi_resp_i.ar_ready;
  assign aw_ready = axi_resp_i.aw_ready;
  assign w_ready  = axi_resp_i.w_ready;
  assign b_valid  = axi_resp_i.b_valid;
  assign r_valid  = axi_resp_i.r_valid;
  assign r_data   = axi_resp_i.r.data;
  assign r_last   = axi_resp_i.r.last;
  
  // Request and response handling
  always_comb begin
    // Default values
    state_d = state_q;
    gnt_o = 1'b0;
    we_o = 1'b0;
    data_o = r_data;
    
    // AXI signals
    axi_req_o = '0;
    ar_sent = 1'b0;
    aw_sent = 1'b0;
    w_sent = 1'b0;
    
    case (state_q)
      IDLE: begin
        // Accept new request
        if (req_i) begin
          gnt_o = 1'b1;
          if (we_i) begin
            // Write request
            state_d = WRITE;
          end else begin
            // Read request
            state_d = READ;
          end
        end
      end
      
      READ: begin
        // Generate AXI read request
        axi_req_o.ar_valid = 1'b1;
        axi_req_o.ar.addr = req_addr_q;
        axi_req_o.ar.size = 3'b011; // 64-bit (8 bytes) transfers
        axi_req_o.ar.burst = 2'b01; // INCR burst
        axi_req_o.ar.len = 8'(DCACHE_LINE_WIDTH/64 - 1); // Calculate burst length
        
        // Handle AXI read response
        axi_req_o.r_ready = 1'b1;
        
        if (ar_ready) begin
          ar_sent = 1'b1;
        end
        
        if (r_valid && r_last) begin
          // Read complete
          we_o = 1'b1;
          state_d = IDLE;
        end
      end
      
      WRITE: begin
        // Generate AXI write request
        axi_req_o.aw_valid = !aw_sent;
        axi_req_o.aw.addr = req_addr_q;
        axi_req_o.aw.size = 3'b011; // 64-bit (8 bytes) transfers
        axi_req_o.aw.burst = 2'b01; // INCR burst
        axi_req_o.aw.len = 8'(DCACHE_LINE_WIDTH/64 - 1); // Calculate burst length
        
        axi_req_o.w_valid = !w_sent;
        axi_req_o.w.data = req_data_q;
        axi_req_o.w.strb = req_be_q;
        axi_req_o.w.last = 1'b1;
        
        axi_req_o.b_ready = 1'b1;
        
        if (aw_ready) begin
          aw_sent = 1'b1;
        end
        
        if (w_ready) begin
          w_sent = 1'b1;
        end
        
        if (b_valid) begin
          // Write complete
          state_d = IDLE;
        end
      end
      
      default: begin
        // Invalid state - return to IDLE
        state_d = IDLE;
      end
    endcase
  end
  
  // State and request registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= IDLE;
      req_addr_q <= '0;
      req_we_q <= 1'b0;
      req_way_q <= '0;
      req_data_q <= '0;
      req_be_q <= '0;
    end else begin
      state_q <= state_d;
      
      if (req_i && gnt_o) begin
        req_addr_q <= addr_i;
        req_we_q <= we_i;
        req_way_q <= way_i;
        req_data_q <= data_i;
        req_be_q <= be_i;
      end
    end
  end

endmodule