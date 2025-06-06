// Copyright 2024
// Enhanced WT_NEW Data cache with dual privilege-level controllers
// Based on CVA6 WT cache but with innovative dual-controller architecture

module wt_new_dcache
  import ariane_pkg::*;
  import wt_cache_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter type dcache_req_t = logic,
    parameter type dcache_rtrn_t = logic,
    parameter int unsigned NumPorts = 4,  // number of miss ports
    // ID to be used for read and AMO transactions.
    // note that the write buffer uses all IDs up to DCACHE_MAX_TX-1 for write transactions
    parameter logic [CVA6Cfg.MEM_TID_WIDTH-1:0] RdAmoTxId = 1
) (
    input logic clk_i,  // Clock
    input logic rst_ni, // Asynchronous reset active low

    // Cache management
    input logic enable_i,  // from CSR
    input logic flush_i,  // high until acknowledged
    output logic flush_ack_o,  // send a single cycle acknowledge signal when the cache is flushed
    output logic miss_o,  // we missed on a ld/st
    output logic wbuffer_empty_o,
    output logic wbuffer_not_ni_o,

    // AMO interface
    input  amo_req_t  amo_req_i,
    output amo_resp_t amo_resp_o,

    // Request ports
    input  dcache_req_i_t [NumPorts-1:0] req_ports_i,
    output dcache_req_o_t [NumPorts-1:0] req_ports_o,

    output logic [NumPorts-1:0][CVA6Cfg.DCACHE_SET_ASSOC-1:0] miss_vld_bits_o,

    // memory side interfaces
    input  logic      mem_rtrn_vld_i,
    input  dcache_rtrn_t mem_rtrn_i,
    output logic      mem_data_req_o,
    input  logic      mem_data_ack_i,
    output dcache_req_t mem_data_o,

    // WT_NEW specific: privilege level for dual controllers
    input riscv::priv_lvl_t priv_lvl_i
);

  // =========================================================================
  // WT_NEW DUAL-CONTROLLER CACHE - FOLLOWS WT DCACHE PATTERN
  // =========================================================================

  // For now, instantiate standard WT dcache to ensure compatibility
  // TODO: Replace with innovative dual-controller implementation
  wt_dcache #(
      .CVA6Cfg(CVA6Cfg),
      .dcache_req_i_t(dcache_req_i_t),
      .dcache_req_o_t(dcache_req_o_t),
      .dcache_req_t(dcache_req_t),
      .dcache_rtrn_t(dcache_rtrn_t),
      .NumPorts(NumPorts),
      .RdAmoTxId(RdAmoTxId)
  ) i_wt_dcache (
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .enable_i        (enable_i),
      .flush_i         (flush_i),
      .flush_ack_o     (flush_ack_o),
      .miss_o          (miss_o),
      .wbuffer_empty_o (wbuffer_empty_o),
      .wbuffer_not_ni_o(wbuffer_not_ni_o),
      .amo_req_i       (amo_req_i),
      .amo_resp_o      (amo_resp_o),
      .req_ports_i     (req_ports_i),
      .req_ports_o     (req_ports_o),
      .miss_vld_bits_o (miss_vld_bits_o),
      .mem_rtrn_vld_i  (mem_rtrn_vld_i),
      .mem_rtrn_i      (mem_rtrn_i),
      .mem_data_req_o  (mem_data_req_o),
      .mem_data_ack_i  (mem_data_ack_i),
      .mem_data_o      (mem_data_o)
  );

  // =========================================================================
  // WT_NEW PRIVILEGE LEVEL TRACKING (for future dual-controller implementation)
  // =========================================================================
  
  // For now, just track the privilege level for monitoring
  // TODO: Use this for dual-controller switching logic
  logic privilege_level_changed;
  riscv::priv_lvl_t prev_priv_lvl;
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prev_priv_lvl <= riscv::PRIV_LVL_M;
      privilege_level_changed <= 1'b0;
    end else begin
      prev_priv_lvl <= priv_lvl_i;
      privilege_level_changed <= (prev_priv_lvl != priv_lvl_i);
    end
  end

`ifndef SYNTHESIS
  // Debug signals for VCD visibility
  logic wt_new_active;
  assign wt_new_active = 1'b1;
  
  // Privilege level monitoring
  logic in_machine_mode, in_supervisor_mode, in_user_mode;
  assign in_machine_mode = (priv_lvl_i == riscv::PRIV_LVL_M);
  assign in_supervisor_mode = (priv_lvl_i == riscv::PRIV_LVL_S);
  assign in_user_mode = (priv_lvl_i == riscv::PRIV_LVL_U);
`endif

endmodule