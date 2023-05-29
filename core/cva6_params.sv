// Copyright 2023 Thales Silicon Security
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON

module cva6_params import ariane_pkg::*; #(
  // Paramaters that can be modified
  parameter ariane_pkg::ariane_cfg_t ArianeCfg = ariane_pkg::ArianeDefaultConfig,
  parameter int unsigned AxiAddrWidth = cva6_config_pkg::CVA6ConfigAxiAddrWidth,
  parameter int unsigned AxiDataWidth = cva6_config_pkg::CVA6ConfigAxiDataWidth,
  parameter int unsigned AxiIdWidth   = cva6_config_pkg::CVA6ConfigAxiIdWidth,
  parameter int unsigned AxiUserWidth = cva6_config_pkg::CVA6ConfigDataUserWidth,
  // WARNING: Do not touch the following parameters
  parameter type axi_ar_chan_t = struct packed {
        logic [AxiIdWidth-1:0]       id;
        logic [AxiAddrWidth-1:0]     addr;
        axi_pkg::len_t               len;
        axi_pkg::size_t              size;
        axi_pkg::burst_t             burst;
        logic                        lock;
        axi_pkg::cache_t             cache;
        axi_pkg::prot_t              prot;
        axi_pkg::qos_t               qos;
        axi_pkg::region_t            region;
        logic [AxiUserWidth-1:0]     user; },
  parameter type axi_aw_chan_t = struct packed {
        logic [AxiIdWidth-1:0]       id;
        logic [AxiAddrWidth-1:0]     addr;
        axi_pkg::len_t               len;
        axi_pkg::size_t              size;
        axi_pkg::burst_t             burst;
        logic                        lock;
        axi_pkg::cache_t             cache;
        axi_pkg::prot_t              prot;
        axi_pkg::qos_t               qos;
        axi_pkg::region_t            region;
        axi_pkg::atop_t              atop;
        logic [AxiUserWidth-1:0]     user; },
  parameter type axi_w_chan_t = struct packed {
        logic [AxiDataWidth-1:0]     data;
        logic [(AxiDataWidth/8)-1:0] strb;
        logic                        last;
        logic [AxiUserWidth-1:0]     user; },
  parameter type b_chan_t = struct packed {
        logic [AxiIdWidth-1:0]       id;
        axi_pkg::resp_t              resp;
        logic [AxiUserWidth-1:0]     user; },
  parameter type r_chan_t = struct packed {
        logic [AxiIdWidth-1:0]       id;
        logic [AxiDataWidth-1:0]     data;
        axi_pkg::resp_t              resp;
        logic                        last;
        logic [AxiUserWidth-1:0]     user; },
  // Paramaters that can be modified
  parameter type axi_req_t = struct packed {
        axi_aw_chan_t                aw;
        logic                        aw_valid;
        axi_w_chan_t                 w;
        logic                        w_valid;
        logic                        b_ready;
        axi_ar_chan_t                ar;
        logic                        ar_valid;
        logic                        r_ready; },
  parameter type axi_rsp_t = struct packed {
        logic                        aw_ready;
        logic                        ar_ready;
        logic                        w_ready;
        logic                        b_valid;
        b_chan_t                     b;
        logic                        r_valid;
        r_chan_t                     r; }
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,
  // Core ID, Cluster ID and boot address are considered more or less static
  input  logic [riscv::VLEN-1:0]       boot_addr_i,  // reset boot address
  input  logic [riscv::XLEN-1:0]       hart_id_i,    // hart id in a multicore environment (reflected in a CSR)

  // Interrupt inputs
  input  logic [1:0]                   irq_i,        // level sensitive IR lines, mip & sip (async)
  input  logic                         ipi_i,        // inter-processor interrupts (async)
  // Timer facilities
  input  logic                         time_irq_i,   // timer interrupt in (async)
  input  logic                         debug_req_i,  // debug request (async)
  // RISC-V formal interface port (`rvfi`):
  // Can be left open when formal tracing is not needed.
  output ariane_pkg::rvfi_port_t       rvfi_o,
  output cvxif_pkg::cvxif_req_t        cvxif_req_o,
  input  cvxif_pkg::cvxif_resp_t       cvxif_resp_i,
  // L15 (memory side)
  output wt_cache_pkg::l15_req_t       l15_req_o,
  input  wt_cache_pkg::l15_rtrn_t      l15_rtrn_i,
  // memory side, AXI Master
  output axi_req_t                     axi_req_o,
  input  axi_rsp_t                     axi_resp_i
);

  cva6 #(
    .ArianeCfg            ( ArianeCfg        ),
    .AxiAddrWidth         ( AxiAddrWidth     ),
    .AxiDataWidth         ( AxiDataWidth     ),
    .AxiIdWidth           ( AxiIdWidth       ),
    .AxiUserWidth         ( AxiUserWidth     ),
    .axi_ar_chan_t        ( axi_ar_chan_t    ),
    .axi_aw_chan_t        ( axi_aw_chan_t    ),
    .axi_w_chan_t         ( axi_w_chan_t     ),
    .b_chan_t             ( b_chan_t         ),
    .r_chan_t             ( r_chan_t         ),
    .axi_req_t            ( axi_req_t        ),
    .axi_rsp_t            ( axi_rsp_t        )
  ) i_cva6 (
    .clk_i                ( clk_i            ),
    .rst_ni               ( rst_ni           ),
    .boot_addr_i          ( boot_addr_i      ),
    .hart_id_i            ( hart_id_i        ),
    .irq_i                ( irq_i            ),
    .ipi_i                ( ipi_i            ),
    .time_irq_i           ( time_irq_i       ),
    .debug_req_i          ( debug_req_i      ),
    .rvfi_o               ( rvfi_o           ),
    .cvxif_req_o          ( cvxif_req_o      ),
    .cvxif_resp_i         ( cvxif_resp_i     ),
    .l15_req_o            ( l15_req_o        ),
    .l15_rtrn_i           ( l15_rtrn_i       ),
    .axi_req_o            ( axi_req_o        ),
    .axi_resp_i           ( axi_resp_i       )
  );

endmodule
