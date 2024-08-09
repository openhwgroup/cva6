// Copyright 2023 Commissariat a l'Energie Atomique et aux Energies
//                Alternatives (CEA)
//
// Licensed under the Solderpad Hardware License, Version 2.1 (the “License”);
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Authors: Cesar Fuguet
// Date: February, 2023
// Description: Wrapper for the Core-V High-Performance L1 data cache (CV-HPDcache)

`include "hpdcache_typedef.svh"

module hpdcache_icache_wrapper
//  Parameters
//  {{{
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter hpdcache_pkg::hpdcache_cfg_t HPDcacheCfg,
    parameter type fetch_dreq_t = logic,
    parameter type fetch_drsp_t = logic,
    parameter type obi_fetch_req_t = logic,
    parameter type obi_fetch_rsp_t = logic,
    parameter int NumPorts = 4,
    parameter int NrHwPrefetchers = 4,

    parameter type cmo_req_t = logic,
    parameter type cmo_rsp_t = logic,
    parameter type hpdcache_mem_addr_t = logic,
    parameter type hpdcache_mem_id_t = logic,
    parameter type hpdcache_mem_data_t = logic,
    parameter type hpdcache_mem_be_t = logic,
    parameter type hpdcache_mem_req_t = logic,
    parameter type hpdcache_mem_req_w_t = logic,
    parameter type hpdcache_mem_resp_r_t = logic,
    parameter type hpdcache_mem_resp_w_t = logic,
    parameter type hpdcache_req_offset_t = logic,
    parameter type hpdcache_data_word_t = logic,
    parameter type hpdcache_req_data_t = logic,
    parameter type hpdcache_req_be_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_tid_t = logic,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic,
    parameter type hpdcache_wbuf_timecnt_t = logic,
    parameter type hpdcache_data_be_t = logic
)
//  }}}

//  Ports
//  {{{
(

    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,

    //  D$
    //  {{{
    //    Cache management
    // Data cache enable - CSR_REGFILE
    input  logic dcache_enable_i,
    // Data cache flush - CONTROLLER
    input  logic dcache_flush_i,
    // Flush acknowledge - CONTROLLER
    output logic dcache_flush_ack_o,
    // Load or store miss - PERF_COUNTERS
    output logic dcache_miss_o,

    // AMO request - EX_STAGE
    input  ariane_pkg::amo_req_t  dcache_amo_req_i,
    // AMO response - EX_STAGE
    output ariane_pkg::amo_resp_t dcache_amo_resp_o,
    // CMO interface request - TO_BE_COMPLETED
    input  cmo_req_t              dcache_cmo_req_i,
    // CMO interface response - TO_BE_COMPLETED
    output cmo_rsp_t              dcache_cmo_resp_o,

    input  fetch_dreq_t    fetch_dreq_i,
    output fetch_drsp_t    fetch_dreq_o,
    input  obi_fetch_req_t fetch_obi_req_i,
    output obi_fetch_rsp_t fetch_obi_rsp_o,

    // Write buffer status to know if empty - EX_STAGE
    output logic wbuffer_empty_o,
    // Write buffer status to know if not non idempotent - EX_STAGE
    output logic wbuffer_not_ni_o,

    //  Hardware memory prefetcher configuration
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0]       hwpf_base_set_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0][63:0] hwpf_base_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic [NrHwPrefetchers-1:0][63:0] hwpf_base_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0]       hwpf_param_set_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0][63:0] hwpf_param_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic [NrHwPrefetchers-1:0][63:0] hwpf_param_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0]       hwpf_throttle_set_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0][63:0] hwpf_throttle_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic [NrHwPrefetchers-1:0][63:0] hwpf_throttle_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic [               63:0]       hwpf_status_o,

    input  logic              dcache_mem_req_miss_read_ready_i,
    output logic              dcache_mem_req_miss_read_valid_o,
    output hpdcache_mem_req_t dcache_mem_req_miss_read_o,

    output logic                 dcache_mem_resp_miss_read_ready_o,
    input  logic                 dcache_mem_resp_miss_read_valid_i,
    input  hpdcache_mem_resp_r_t dcache_mem_resp_miss_read_i,

    input  logic              dcache_mem_req_wbuf_write_ready_i,
    output logic              dcache_mem_req_wbuf_write_valid_o,
    output hpdcache_mem_req_t dcache_mem_req_wbuf_write_o,

    input  logic                dcache_mem_req_wbuf_write_data_ready_i,
    output logic                dcache_mem_req_wbuf_write_data_valid_o,
    output hpdcache_mem_req_w_t dcache_mem_req_wbuf_write_data_o,

    output logic                 dcache_mem_resp_wbuf_write_ready_o,
    input  logic                 dcache_mem_resp_wbuf_write_valid_i,
    input  hpdcache_mem_resp_w_t dcache_mem_resp_wbuf_write_i,

    input  logic              dcache_mem_req_uc_read_ready_i,
    output logic              dcache_mem_req_uc_read_valid_o,
    output hpdcache_mem_req_t dcache_mem_req_uc_read_o,

    output logic                 dcache_mem_resp_uc_read_ready_o,
    input  logic                 dcache_mem_resp_uc_read_valid_i,
    input  hpdcache_mem_resp_r_t dcache_mem_resp_uc_read_i,

    input  logic              dcache_mem_req_uc_write_ready_i,
    output logic              dcache_mem_req_uc_write_valid_o,
    output hpdcache_mem_req_t dcache_mem_req_uc_write_o,

    input  logic                dcache_mem_req_uc_write_data_ready_i,
    output logic                dcache_mem_req_uc_write_data_valid_o,
    output hpdcache_mem_req_w_t dcache_mem_req_uc_write_data_o,

    output logic                 dcache_mem_resp_uc_write_ready_o,
    input  logic                 dcache_mem_resp_uc_write_valid_i,
    input  hpdcache_mem_resp_w_t dcache_mem_resp_uc_write_i,

    input logic [HPDcacheCfg.u.memIdWidth-1:0] HPDCACHE_UC_READ_ID,
    input logic [HPDcacheCfg.u.memIdWidth-1:0] HPDCACHE_UC_WRITE_ID

);
  localparam int HPDCACHE_NREQUESTERS = NumPorts + 2;

  typedef logic [63:0] hwpf_stride_param_t;

  logic                        dcache_req_valid[HPDCACHE_NREQUESTERS-1:0];
  logic                        dcache_req_ready[HPDCACHE_NREQUESTERS-1:0];
  hpdcache_req_t               dcache_req      [HPDCACHE_NREQUESTERS-1:0];
  logic                        dcache_req_abort[HPDCACHE_NREQUESTERS-1:0];
  hpdcache_tag_t               dcache_req_tag  [HPDCACHE_NREQUESTERS-1:0];
  hpdcache_pkg::hpdcache_pma_t dcache_req_pma  [HPDCACHE_NREQUESTERS-1:0];
  logic                        dcache_rsp_valid[HPDCACHE_NREQUESTERS-1:0];
  hpdcache_rsp_t               dcache_rsp      [HPDCACHE_NREQUESTERS-1:0];
  logic dcache_read_miss, dcache_write_miss;

  logic                                                         snoop_valid;
  logic                                                         snoop_abort;
  hpdcache_req_offset_t                                         snoop_addr_offset;
  hpdcache_tag_t                                                snoop_addr_tag;
  logic                                                         snoop_phys_indexed;

  logic                                                         dcache_cmo_req_is_prefetch;

  hwpf_stride_pkg::hwpf_stride_throttle_t [NrHwPrefetchers-1:0] hwpf_throttle_in;
  hwpf_stride_pkg::hwpf_stride_throttle_t [NrHwPrefetchers-1:0] hwpf_throttle_out;

  generate
    for (genvar r = 0; r < (1); r++) begin : gen_cva6_hpdcache_load_if_adapter

      cva6_hpdcache_icache_if_adapter #(
          .CVA6Cfg              (CVA6Cfg),
          .hpdcacheCfg          (HPDcacheCfg),
          .hpdcache_tag_t       (hpdcache_tag_t),
          .hpdcache_req_offset_t(hpdcache_req_offset_t),
          .hpdcache_req_sid_t   (hpdcache_req_sid_t),
          .hpdcache_req_t       (hpdcache_req_t),
          .hpdcache_rsp_t       (hpdcache_rsp_t),
          .fetch_dreq_t         (fetch_dreq_t),
          .fetch_drsp_t         (fetch_drsp_t),
          .obi_fetch_req_t      (obi_fetch_req_t),
          .obi_fetch_rsp_t      (obi_fetch_rsp_t),
          //   .is_load_port         (1'b1)
      ) i_cva6_hpdcache_load_if_adapter (
          .clk_i,
          .rst_ni,

          .hpdcache_req_sid_i(hpdcache_req_sid_t'(r)),

          .dreq_i(fetch_dreq_i),
          .dreq_o(fetch_dreq_o),
          .fetch_obi_req_i(fetch_obi_req_i),
          .fetch_obi_rsp_o(fetch_obi_rsp_o),

          .hpdcache_req_valid_o(dcache_req_valid[r]),
          .hpdcache_req_ready_i(dcache_req_ready[r]),
          .hpdcache_req_o      (dcache_req[r]),
          .hpdcache_req_abort_o(dcache_req_abort[r]),
          .hpdcache_req_tag_o  (dcache_req_tag[r]),
          .hpdcache_req_pma_o  (dcache_req_pma[r]),

          .hpdcache_rsp_valid_i(dcache_rsp_valid[r]),
          .hpdcache_rsp_i      (dcache_rsp[r])
      );
    end
  endgenerate

  //  Snoop load port
  assign snoop_valid = dcache_req_valid[0] & dcache_req_ready[0],
      snoop_abort = dcache_req_abort[0],
      snoop_addr_offset = dcache_req[0].addr_offset,
      snoop_addr_tag = dcache_req_tag[0],
      snoop_phys_indexed = dcache_req[0].phys_indexed;

  generate
    for (genvar h = 0; h < NrHwPrefetchers; h++) begin : gen_hwpf_throttle
      assign hwpf_throttle_in[h] = hwpf_stride_pkg::hwpf_stride_throttle_t'(hwpf_throttle_i[h]);
      assign hwpf_throttle_o[h]  = hwpf_stride_pkg::hwpf_stride_param_t'(hwpf_throttle_out[h]);
    end
  endgenerate

  hwpf_stride_wrapper #(
      .hpdcacheCfg          (HPDcacheCfg),
      .NUM_HW_PREFETCH      (NrHwPrefetchers),
      .NUM_SNOOP_PORTS      (1),
      .hpdcache_tag_t       (hpdcache_tag_t),
      .hpdcache_req_offset_t(hpdcache_req_offset_t),
      .hpdcache_req_data_t  (hpdcache_req_data_t),
      .hpdcache_req_be_t    (hpdcache_req_be_t),
      .hpdcache_req_sid_t   (hpdcache_req_sid_t),
      .hpdcache_req_tid_t   (hpdcache_req_tid_t),
      .hpdcache_req_t       (hpdcache_req_t),
      .hpdcache_rsp_t       (hpdcache_rsp_t)
  ) i_hwpf_stride_wrapper (
      .clk_i,
      .rst_ni,

      .hwpf_stride_base_set_i    (hwpf_base_set_i),
      .hwpf_stride_base_i        (hwpf_base_i),
      .hwpf_stride_base_o        (hwpf_base_o),
      .hwpf_stride_param_set_i   (hwpf_param_set_i),
      .hwpf_stride_param_i       (hwpf_param_i),
      .hwpf_stride_param_o       (hwpf_param_o),
      .hwpf_stride_throttle_set_i(hwpf_throttle_set_i),
      .hwpf_stride_throttle_i    (hwpf_throttle_in),
      .hwpf_stride_throttle_o    (hwpf_throttle_out),
      .hwpf_stride_status_o      (hwpf_status_o),

      .snoop_valid_i       (snoop_valid),
      .snoop_abort_i       (snoop_abort),
      .snoop_addr_offset_i (snoop_addr_offset),
      .snoop_addr_tag_i    (snoop_addr_tag),
      .snoop_phys_indexed_i(snoop_phys_indexed),

      .hpdcache_req_sid_i(hpdcache_req_sid_t'(NumPorts)),

      .hpdcache_req_valid_o(dcache_req_valid[NumPorts]),
      .hpdcache_req_ready_i(dcache_req_ready[NumPorts]),
      .hpdcache_req_o      (dcache_req[NumPorts]),
      .hpdcache_req_abort_o(dcache_req_abort[NumPorts]),
      .hpdcache_req_tag_o  (dcache_req_tag[NumPorts]),
      .hpdcache_req_pma_o  (dcache_req_pma[NumPorts]),
      .hpdcache_rsp_valid_i(dcache_rsp_valid[NumPorts]),
      .hpdcache_rsp_i      (dcache_rsp[NumPorts])
  );

  // localparam logic [HPDcacheCfg.u.memIdWidth-1:0] HPDCACHE_UC_READ_ID = 8;

  hpdcache #(
      .hpdcacheCfg          (HPDcacheCfg),
      .wbuf_timecnt_t       (hpdcache_wbuf_timecnt_t),
      .hpdcache_tag_t       (hpdcache_tag_t),
      .hpdcache_data_word_t (hpdcache_data_word_t),
      .hpdcache_data_be_t   (hpdcache_data_be_t),
      .hpdcache_req_offset_t(hpdcache_req_offset_t),
      .hpdcache_req_data_t  (hpdcache_req_data_t),
      .hpdcache_req_be_t    (hpdcache_req_be_t),
      .hpdcache_req_sid_t   (hpdcache_req_sid_t),
      .hpdcache_req_tid_t   (hpdcache_req_tid_t),
      .hpdcache_req_t       (hpdcache_req_t),
      .hpdcache_rsp_t       (hpdcache_rsp_t),
      .hpdcache_mem_addr_t  (hpdcache_mem_addr_t),
      .hpdcache_mem_id_t    (hpdcache_mem_id_t),
      .hpdcache_mem_data_t  (hpdcache_mem_data_t),
      .hpdcache_mem_be_t    (hpdcache_mem_be_t),
      .hpdcache_mem_req_t   (hpdcache_mem_req_t),
      .hpdcache_mem_req_w_t (hpdcache_mem_req_w_t),
      .hpdcache_mem_resp_r_t(hpdcache_mem_resp_r_t),
      .hpdcache_mem_resp_w_t(hpdcache_mem_resp_w_t)
  ) i_hpdcache (
      .clk_i,
      .rst_ni,

      .wbuf_flush_i(dcache_flush_i),

      .core_req_valid_i(dcache_req_valid),
      .core_req_ready_o(dcache_req_ready),
      .core_req_i      (dcache_req),
      .core_req_abort_i(dcache_req_abort),
      .core_req_tag_i  (dcache_req_tag),
      .core_req_pma_i  (dcache_req_pma),

      .core_rsp_valid_o(dcache_rsp_valid),
      .core_rsp_o      (dcache_rsp),

      .mem_req_miss_read_ready_i(dcache_mem_req_miss_read_ready_i),
      .mem_req_miss_read_valid_o(dcache_mem_req_miss_read_valid_o),
      .mem_req_miss_read_o      (dcache_mem_req_miss_read_o),

      .mem_resp_miss_read_ready_o(dcache_mem_resp_miss_read_ready_o),
      .mem_resp_miss_read_valid_i(dcache_mem_resp_miss_read_valid_i),
      .mem_resp_miss_read_i      (dcache_mem_resp_miss_read_i),

      .mem_req_wbuf_write_ready_i('0),
      .mem_req_wbuf_write_valid_o(  /* unused */),
      .mem_req_wbuf_write_o      (  /* unused */),

      .mem_req_wbuf_write_data_ready_i('0),
      .mem_req_wbuf_write_data_valid_o(  /* unused */),
      .mem_req_wbuf_write_data_o      (  /* unused */),

      .mem_resp_wbuf_write_ready_o(  /* unused */),
      .mem_resp_wbuf_write_valid_i('0),
      .mem_resp_wbuf_write_i      (  /* unused */),

      .mem_req_uc_read_ready_i(dcache_mem_req_uc_read_ready_i),
      .mem_req_uc_read_valid_o(dcache_mem_req_uc_read_valid_o),
      .mem_req_uc_read_o      (dcache_mem_req_uc_read_o),

      .mem_resp_uc_read_ready_o(dcache_mem_resp_uc_read_ready_o),
      .mem_resp_uc_read_valid_i(dcache_mem_resp_uc_read_valid_i),
      .mem_resp_uc_read_i      (dcache_mem_resp_uc_read_i),

      .mem_req_uc_write_ready_i('0),
      .mem_req_uc_write_valid_o(  /* unused */),
      .mem_req_uc_write_o      (  /* unused */),

      .mem_req_uc_write_data_ready_i('0),
      .mem_req_uc_write_data_valid_o(  /* unused */),
      .mem_req_uc_write_data_o      (  /* unused */),

      .mem_resp_uc_write_ready_o(  /* unused */),
      .mem_resp_uc_write_valid_i('0),
      .mem_resp_uc_write_i      (  /* unused */),

      .evt_cache_write_miss_o(  /* unused */),
      .evt_cache_read_miss_o (dcache_read_miss),
      .evt_uncached_req_o    (  /* unused */),
      .evt_cmo_req_o         (  /* unused */),
      .evt_write_req_o       (  /* unused */),
      .evt_read_req_o        (  /* unused */),
      .evt_prefetch_req_o    (  /* unused */),
      .evt_req_on_hold_o     (  /* unused */),
      .evt_rtab_rollback_o   (  /* unused */),
      .evt_stall_refill_o    (  /* unused */),
      .evt_stall_o           (  /* unused */),

      .wbuf_empty_o(  /* unused */),

      .cfg_enable_i                       (dcache_enable_i),
      .cfg_wbuf_threshold_i               (3'd2),
      .cfg_wbuf_reset_timecnt_on_write_i  (1'b1),
      .cfg_wbuf_sequential_waw_i          (1'b0),
      .cfg_wbuf_inhibit_write_coalescing_i(1'b0),
      .cfg_prefetch_updt_plru_i           (1'b1),
      .cfg_error_on_cacheable_amo_i       (1'b0),
      .cfg_rtab_single_entry_i            (1'b0),
      .HPDCACHE_UC_READ_ID                (HPDCACHE_UC_READ_ID),
      .HPDCACHE_UC_WRITE_ID               (HPDCACHE_UC_WRITE_ID)
  );

  assign dcache_miss_o = dcache_read_miss, wbuffer_not_ni_o = wbuffer_empty_o;

  always_ff @(posedge clk_i or negedge rst_ni) begin : dcache_flush_ff
    if (!rst_ni) dcache_flush_ack_o <= 1'b0;
    else dcache_flush_ack_o <= ~dcache_flush_ack_o & dcache_flush_i;
  end

  //  }}}

endmodule : hpdcache_icache_wrapper
