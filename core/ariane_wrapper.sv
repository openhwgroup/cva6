// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.com)

module ariane_wrapper import ariane_pkg::*; #(
  parameter ariane_pkg::ariane_cfg_t ArianeCfg     = ariane_pkg::ArianeDefaultConfig
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,
  // Core ID, Cluster ID and boot address are considered more or less static
  input  logic [63:0]                  boot_addr_i,  // reset boot address
  input  logic [63:0]                  hart_id_i,    // hart id in a multicore environment (reflected in a CSR)

  // Interrupt inputs
  input  logic [1:0]                   irq_i,        // level sensitive IR lines, mip & sip (async)
  input  logic                         ipi_i,        // inter-processor interrupts (async)
  // Timer facilities
  input  logic                         time_irq_i,   // timer interrupt in (async)
  input  logic                         debug_req_i,  // debug request (async)
`ifdef FIRESIM_TRACE
  // firesim trace port
  output traced_instr_pkg::trace_port_t trace_o,
`endif
  // RISC-V formal interface port (`rvfi`):
  // Can be left open when formal tracing is not needed.
  output logic                         rvfi_valid_1,
  output logic[63:0]                   rvfi_order_1,
  output logic[31:0]                   rvfi_insn_1,
  output logic                         rvfi_trap_1,
  output logic                         rvfi_halt_1,
  output logic                         rvfi_intr_1,
  output logic[2:0]                    rvfi_mode_1,
  output logic[2:0]                    rvfi_ixl_1,
  output logic[4:0]                    rvfi_rs1_addr_1,
  output logic[4:0]                    rvfi_rs2_addr_1,
  output logic[riscv::XLEN-1:0]        rvfi_rs1_rdata_1,
  output logic[riscv::XLEN-1:0]        rvfi_rs2_rdata_1,
  output logic[4:0]                    rvfi_rd_addr_1,
  output logic[riscv::XLEN-1:0]        rvfi_rd_wdata_1,
  output logic[riscv::XLEN-1:0]        rvfi_pc_rdata_1,
  output logic[riscv::XLEN-1:0]        rvfi_pc_wdata_1,
  output logic[riscv::XLEN-1:0]        rvfi_mem_addr_1,
  output logic[(riscv::XLEN)/8-1:0]    rvfi_mem_rmask_1,
  output logic[(riscv::XLEN)/8-1:0]    rvfi_mem_wmask_1,
  output logic[riscv::XLEN-1:0]        rvfi_mem_rdata_1,
  output logic[riscv::XLEN-1:0]        rvfi_mem_wdata_1,
  output logic                         rvfi_valid_0,
  output logic[63:0]                   rvfi_order_0,
  output logic[31:0]                   rvfi_insn_0,
  output logic                         rvfi_trap_0,
  output logic                         rvfi_halt_0,
  output logic                         rvfi_intr_0,
  output logic[2:0]                    rvfi_mode_0,
  output logic[2:0]                    rvfi_ixl_0,
  output logic[4:0]                    rvfi_rs1_addr_0,
  output logic[4:0]                    rvfi_rs2_addr_0,
  output logic[riscv::XLEN-1:0]        rvfi_rs1_rdata_0,
  output logic[riscv::XLEN-1:0]        rvfi_rs2_rdata_0,
  output logic[4:0]                    rvfi_rd_addr_0,
  output logic[riscv::XLEN-1:0]        rvfi_rd_wdata_0,
  output logic[riscv::XLEN-1:0]        rvfi_pc_rdata_0,
  output logic[riscv::XLEN-1:0]        rvfi_pc_wdata_0,
  output logic[riscv::XLEN-1:0]        rvfi_mem_addr_0,
  output logic[(riscv::XLEN)/8-1:0]    rvfi_mem_rmask_0,
  output logic[(riscv::XLEN)/8-1:0]    rvfi_mem_wmask_0,
  output logic[riscv::XLEN-1:0]        rvfi_mem_rdata_0,
  output logic[riscv::XLEN-1:0]        rvfi_mem_wdata_0,
`ifdef PITON_ARIANE
  // L15 (memory side)
  output wt_cache_pkg::l15_req_t       l15_req_o,
  input  wt_cache_pkg::l15_rtrn_t      l15_rtrn_i
`else
  // memory side, AXI Master
  output ariane_axi::id_t              aw_id_o,
  output ariane_axi::addr_t            aw_addr_o,
  output axi_pkg::len_t                aw_len_o,
  output axi_pkg::size_t               aw_size_o,
  output axi_pkg::burst_t              aw_burst_o,
  output logic                         aw_lock_o,
  output axi_pkg::cache_t              aw_cache_o,
  output axi_pkg::prot_t               aw_prot_o,
  output axi_pkg::qos_t                aw_qos_o,
  output axi_pkg::region_t             aw_region_o,
  output axi_pkg::atop_t               aw_atop_o,
  output ariane_axi::user_t            aw_user_o,
  output logic                         aw_valid_o,
  output ariane_axi::data_t            w_data_o,
  output ariane_axi::strb_t            w_strb_o,
  output logic                         w_last_o,
  output ariane_axi::user_t            w_user_o,
  output logic                         w_valid_o,
  output logic                         b_ready_o,
  output ariane_axi::id_t              ar_id_o,
  output ariane_axi::addr_t            ar_addr_o,
  output axi_pkg::len_t                ar_len_o,
  output axi_pkg::size_t               ar_size_o,
  output axi_pkg::burst_t              ar_burst_o,
  output logic                         ar_lock_o,
  output axi_pkg::cache_t              ar_cache_o,
  output axi_pkg::prot_t               ar_prot_o,
  output axi_pkg::qos_t                ar_qos_o,
  output axi_pkg::region_t             ar_region_o,
  output ariane_axi::user_t            ar_user_o,
  output logic                         ar_valid_o,
  output logic                         r_ready_o,
  input  logic                         aw_ready_i,
  input  logic                         ar_ready_i,
  input  logic                         w_ready_i,
  input  logic                         b_valid_i,
  input  ariane_axi::id_t              b_id_i,
  input  axi_pkg::resp_t               b_resp_i,
  input  ariane_axi::user_t            b_user_i,
  input  logic                         r_valid_i,
  input  ariane_axi::id_t              r_id_i,
  input  ariane_axi::data_t            r_data_i,
  input  axi_pkg::resp_t               r_resp_i,
  input  logic                         r_last_i,
  input  ariane_axi::user_t            r_user_i
`endif
);

  ariane_axi::req_t               axi_ariane_req;
  ariane_axi::resp_t              axi_ariane_resp;
  ariane_rvfi_pkg::rvfi_port_t    rvfi;

  assign aw_id_o                  = axi_ariane_req.aw.id;
  assign aw_addr_o                = axi_ariane_req.aw.addr;
  assign aw_len_o                 = axi_ariane_req.aw.len;
  assign aw_size_o                = axi_ariane_req.aw.size;
  assign aw_burst_o               = axi_ariane_req.aw.burst;
  assign aw_lock_o                = axi_ariane_req.aw.lock;
  assign aw_cache_o               = axi_ariane_req.aw.cache;
  assign aw_prot_o                = axi_ariane_req.aw.prot;
  assign aw_qos_o                 = axi_ariane_req.aw.qos;
  assign aw_region_o              = axi_ariane_req.aw.region;
  assign aw_atop_o                = axi_ariane_req.aw.atop;
  assign aw_user_o                = axi_ariane_req.aw.user;
  assign aw_valid_o               = axi_ariane_req.aw_valid;
  assign w_data_o                 = axi_ariane_req.w.data;
  assign w_strb_o                 = axi_ariane_req.w.strb;
  assign w_last_o                 = axi_ariane_req.w.last;
  assign w_user_o                 = axi_ariane_req.w.user;
  assign w_valid_o                = axi_ariane_req.w_valid;
  assign b_ready_o                = axi_ariane_req.b_ready;
  assign ar_id_o                  = axi_ariane_req.ar.id;
  assign ar_addr_o                = axi_ariane_req.ar.addr;
  assign ar_len_o                 = axi_ariane_req.ar.len;
  assign ar_size_o                = axi_ariane_req.ar.size;
  assign ar_burst_o               = axi_ariane_req.ar.burst;
  assign ar_lock_o                = axi_ariane_req.ar.lock;
  assign ar_cache_o               = axi_ariane_req.ar.cache;
  assign ar_prot_o                = axi_ariane_req.ar.prot;
  assign ar_qos_o                 = axi_ariane_req.ar.qos;
  assign ar_region_o              = axi_ariane_req.ar.region;
  assign ar_user_o                = axi_ariane_req.ar.user;
  assign ar_valid_o               = axi_ariane_req.ar_valid;
  assign r_ready_o                = axi_ariane_req.r_ready;

  assign axi_ariane_resp.aw_ready = aw_ready_i;
  assign axi_ariane_resp.ar_ready = ar_ready_i;
  assign axi_ariane_resp.w_ready  = w_ready_i;
  assign axi_ariane_resp.b_valid  = b_valid_i;
  assign axi_ariane_resp.b.id     = b_id_i;
  assign axi_ariane_resp.b.resp   = b_resp_i;
  assign axi_ariane_resp.b.user   = b_user_i;
  assign axi_ariane_resp.r_valid  = r_valid_i;
  assign axi_ariane_resp.r.id     = r_id_i;
  assign axi_ariane_resp.r.data   = r_data_i;
  assign axi_ariane_resp.r.resp   = r_resp_i;
  assign axi_ariane_resp.r.last   = r_last_i;
  assign axi_ariane_resp.r.user   = r_user_i;

  assign rvfi_valid_1             = rvfi[1].valid;
  assign rvfi_order_1             = rvfi[1].order;
  assign rvfi_insn_1              = rvfi[1].insn;
  assign rvfi_trap_1              = rvfi[1].trap;
  assign rvfi_halt_1              = rvfi[1].halt;
  assign rvfi_intr_1              = rvfi[1].intr;
  assign rvfi_mode_1              = rvfi[1].mode;
  assign rvfi_ixl_1               = rvfi[1].ixl;
  assign rvfi_rs1_addr_1          = rvfi[1].rs1_addr;
  assign rvfi_rs2_addr_1          = rvfi[1].rs2_addr;
  assign rvfi_rs1_rdata_1         = rvfi[1].rs1_rdata;
  assign rvfi_rs2_rdata_1         = rvfi[1].rs2_rdata;
  assign rvfi_rd_addr_1           = rvfi[1].rd_addr;
  assign rvfi_rd_wdata_1          = rvfi[1].rd_wdata;
  assign rvfi_pc_rdata_1          = rvfi[1].pc_rdata;
  assign rvfi_pc_wdata_1          = rvfi[1].pc_wdata;
  assign rvfi_mem_addr_1          = rvfi[1].mem_addr;
  assign rvfi_mem_rmask_1         = rvfi[1].mem_rmask;
  assign rvfi_mem_wmask_1         = rvfi[1].mem_wmask;
  assign rvfi_mem_rdata_1         = rvfi[1].mem_rdata;
  assign rvfi_mem_wdata_1         = rvfi[1].mem_wdata;
  assign rvfi_valid_0             = rvfi[0].valid;
  assign rvfi_order_0             = rvfi[0].order;
  assign rvfi_insn_0              = rvfi[0].insn;
  assign rvfi_trap_0              = rvfi[0].trap;
  assign rvfi_halt_0              = rvfi[0].halt;
  assign rvfi_intr_0              = rvfi[0].intr;
  assign rvfi_mode_0              = rvfi[0].mode;
  assign rvfi_ixl_0               = rvfi[0].ixl;
  assign rvfi_rs1_addr_0          = rvfi[0].rs1_addr;
  assign rvfi_rs2_addr_0          = rvfi[0].rs2_addr;
  assign rvfi_rs1_rdata_0         = rvfi[0].rs1_rdata;
  assign rvfi_rs2_rdata_0         = rvfi[0].rs2_rdata;
  assign rvfi_rd_addr_0           = rvfi[0].rd_addr;
  assign rvfi_rd_wdata_0          = rvfi[0].rd_wdata;
  assign rvfi_pc_rdata_0          = rvfi[0].pc_rdata;
  assign rvfi_pc_wdata_0          = rvfi[0].pc_wdata;
  assign rvfi_mem_addr_0          = rvfi[0].mem_addr;
  assign rvfi_mem_rmask_0         = rvfi[0].mem_rmask;
  assign rvfi_mem_wmask_0         = rvfi[0].mem_wmask;
  assign rvfi_mem_rdata_0         = rvfi[0].mem_rdata;
  assign rvfi_mem_wdata_0         = rvfi[0].mem_wdata;

  ariane #(
    .ArianeCfg  ( ariane_soc::ArianeSocCfg )
  ) i_ariane (
    .clk_i                ( clk_i           ),
    .rst_ni               ( rst_ni          ),
    .boot_addr_i          ( boot_addr_i     ),
    .hart_id_i            ( hart_id_i       ),
    .irq_i                ( irq_i           ),
    .ipi_i                ( ipi_i           ),
    .time_irq_i           ( time_irq_i      ),
    .rvfi_o               ( rvfi            ),
    .debug_req_i          ( debug_req_i     ),
    .axi_req_o            ( axi_ariane_req  ),
    .axi_resp_i           ( axi_ariane_resp )
  );

endmodule // ariane_wrapper
