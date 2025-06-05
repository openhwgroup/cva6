// Copyright 2024 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// WT_NEW Cache Subsystem Adapter
// Bridges the WT_NEW cache (with privilege-level dual controllers) to the 
// standard CVA6 cache subsystem interface

module wt_new_cache_subsystem_adapter
  import ariane_pkg::*;
  import wt_cache_pkg::*;
  import wt_new_cache_pkg::*;
  #(parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type icache_areq_t = logic,
    parameter type icache_arsp_t = logic,
    parameter type icache_dreq_t = logic,
    parameter type icache_drsp_t = logic,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter type icache_req_t = logic,
    parameter type icache_rtrn_t = logic,
    parameter int unsigned NumPorts = 4,
    parameter type noc_req_t = logic,
    parameter type noc_resp_t = logic)
   (
    input logic clk_i,
    input logic rst_ni,
    input logic [1:0] priv_lvl_i,  // KEY: Privilege level for WT_NEW dual controllers
    
    // I$ interface (passthrough - WT_NEW only affects dcache)
    input logic icache_en_i,
    input logic icache_flush_i,
    output logic icache_miss_o,
    input icache_areq_t icache_areq_i,
    output icache_arsp_t icache_areq_o,
    input icache_dreq_t icache_dreq_i,
    output icache_drsp_t icache_dreq_o,
    
    // D$ interface (adapted to WT_NEW)
    input logic dcache_enable_i,
    input logic dcache_flush_i,
    output logic dcache_flush_ack_o,
    output logic dcache_miss_o,
    output logic [NumPorts-1:0][CVA6Cfg.DCACHE_SET_ASSOC-1:0] miss_vld_bits_o,
    input amo_req_t dcache_amo_req_i,
    output amo_resp_t dcache_amo_resp_o,
    input dcache_req_i_t [NumPorts-1:0] dcache_req_ports_i,
    output dcache_req_o_t [NumPorts-1:0] dcache_req_ports_o,
    output logic wbuffer_empty_o,
    output logic wbuffer_not_ni_o,
    
    // Memory interface
    output noc_req_t noc_req_o,
    input noc_resp_t noc_resp_i,
    input logic [63:0] inval_addr_i,
    input logic inval_valid_i,
    output logic inval_ready_o
   );

   // =========================================================================
   // ICACHE PASSTHROUGH - WT_NEW only affects DCACHE
   // =========================================================================
   
   // For now, use standard icache (WT_NEW is dcache innovation)
   cva6_icache #(
     .CVA6Cfg(CVA6Cfg),
     .icache_areq_t(icache_areq_t),
     .icache_arsp_t(icache_arsp_t),
     .icache_dreq_t(icache_dreq_t),
     .icache_drsp_t(icache_drsp_t),
     .icache_req_t(icache_req_t),
     .icache_rtrn_t(icache_rtrn_t)
   ) i_cva6_icache (
     .clk_i(clk_i),
     .rst_ni(rst_ni),
     .en_i(icache_en_i),
     .flush_i(icache_flush_i),
     .miss_o(icache_miss_o),
     .areq_i(icache_areq_i),
     .areq_o(icache_areq_o),
     .dreq_i(icache_dreq_i),
     .dreq_o(icache_dreq_o),
     .mem_rtrn_vld_i(1'b0),
     .mem_rtrn_i('0),
     .mem_data_req_o(),
     .mem_data_ack_i(1'b0),
     .mem_data_o()
   );

   // =========================================================================
   // WT_NEW DCACHE INTEGRATION
   // =========================================================================
   
   // Signal to indicate WT_NEW is active (visible in VCD)
   logic wt_new_cache_active;
   assign wt_new_cache_active = 1'b1;
   
   // Cache type override for VCD visibility
   logic [3:0] effective_dcache_type;
   assign effective_dcache_type = 4'd8; // WT_NEW value
   
   // =========================================================================
   // PRIVILEGE LEVEL MODIFIER FOR TESTING
   // =========================================================================
   
   // Modified privilege level for WT_NEW cache testing
   riscv::priv_lvl_t modified_priv_lvl;
   logic [31:0] priv_modifier_cycle_counter;
   logic priv_modifier_switch_event;
   logic priv_modifier_in_machine_mode;
   logic priv_modifier_in_user_mode;
   
   // Instantiate privilege level modifier
   priv_lvl_modifier #(
     .SWITCH_PERIOD(100)  // Switch every 100 clock cycles
   ) i_priv_lvl_modifier (
     .clk_i(clk_i),
     .rst_ni(rst_ni),
     .actual_priv_lvl_i(priv_lvl_i),           // Actual privilege level (ignored)
     .modified_priv_lvl_o(modified_priv_lvl),  // Modified privilege level for testing
     .cycle_counter_o(priv_modifier_cycle_counter),
     .privilege_switch_event_o(priv_modifier_switch_event),
     .in_machine_mode_o(priv_modifier_in_machine_mode),
     .in_user_mode_o(priv_modifier_in_user_mode)
   );
   
   // Privilege level tracking for debugging
   riscv::priv_lvl_t current_priv_lvl;
   assign current_priv_lvl = modified_priv_lvl; // Use modified privilege level
   
   // Port arbitration - simplified approach for initial implementation
   logic dcache_req_valid;
   logic [CVA6Cfg.PLEN-1:0] dcache_req_addr;
   logic dcache_req_we;
   logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] dcache_req_wdata;
   logic [CVA6Cfg.DCACHE_LINE_WIDTH-1:0] dcache_resp_rdata;
   logic dcache_resp_hit;
   
   // Simple port arbitration (Port 0 priority for initial implementation)
   assign dcache_req_valid = dcache_req_ports_i[0].data_req;
   assign dcache_req_addr  = {{CVA6Cfg.PLEN-CVA6Cfg.XLEN{1'b0}}, dcache_req_ports_i[0].address_tag, dcache_req_ports_i[0].address_index};
   assign dcache_req_we    = dcache_req_ports_i[0].data_we;
   assign dcache_req_wdata = dcache_req_ports_i[0].data_wdata;
   
   // Instantiate the actual WT_NEW cache with modified privilege level
   wt_new_cache_subsystem #(
     .CVA6Cfg(CVA6Cfg),
     .NUM_DUAL_SETS(wt_new_cache_pkg::NUM_DUAL_SETS)
   ) i_wt_new_cache (
     .clk_i(clk_i),
     .rst_ni(rst_ni),
     .priv_lvl_i(modified_priv_lvl),  // KEY: Use modified privilege level for predictable switching
     
     // Cache interface
     .req_i(dcache_req_valid & dcache_enable_i),
     .addr_i(dcache_req_addr),
     .we_i(dcache_req_we),
     .wdata_i(dcache_req_wdata),
     .rdata_o(dcache_resp_rdata),
     .hit_o(dcache_resp_hit)
   );
   
   // Map responses back to ports
   always_comb begin
     // Initialize all ports
     for (int i = 0; i < NumPorts; i++) begin
       dcache_req_ports_o[i] = '0;
     end
     
     // Port 0 gets the response
     dcache_req_ports_o[0].data_rvalid = dcache_req_valid & dcache_resp_hit;
     dcache_req_ports_o[0].data_rdata  = dcache_resp_rdata;
     dcache_req_ports_o[0].data_gnt    = dcache_req_valid; // Simple grant
   end
   
   // =========================================================================
   // SIMPLIFIED IMPLEMENTATIONS FOR INITIAL TESTING
   // =========================================================================
   
   // Cache control signals
   assign dcache_flush_ack_o = dcache_flush_i; // Immediate ack for now
   assign dcache_miss_o = dcache_req_valid & ~dcache_resp_hit;
   assign miss_vld_bits_o = '0; // Not implemented yet
   
   // AMO operations (not implemented in WT_NEW yet)
   assign dcache_amo_resp_o = '0;
   
   // Write buffer (WT_NEW is write-through, so always empty)
   assign wbuffer_empty_o = 1'b1;
   assign wbuffer_not_ni_o = 1'b0;
   
   // Memory interface (simplified - direct passthrough for now)
   // In full implementation, this would handle cache misses to memory
   assign noc_req_o = '0;
   assign inval_ready_o = 1'b1;

endmodule