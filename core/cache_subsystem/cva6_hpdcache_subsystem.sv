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
// Description: CVA6 cache subsystem integrating standard CVA6's
//              instruction cache and the Core-V High-Performance L1
//              data cache (CV-HPDcache).

module cva6_hpdcache_subsystem
//  Parameters
//  {{{
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter int NumPorts = 4,
    parameter int NrHwPrefetchers = 4,
    parameter type noc_req_t = logic,
    parameter type noc_resp_t = logic,
    parameter type cmo_req_t = logic,
    parameter type cmo_rsp_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input logic clk_i,
    input logic rst_ni,

    //  I$
    //  {{{
    input logic icache_en_i,  // enable icache (or bypass e.g: in debug mode)
    input logic icache_flush_i,  // flush the icache, flush and kill have to be asserted together
    output logic icache_miss_o,  // to performance counter
    // address translation requests
    input ariane_pkg::icache_areq_t icache_areq_i,  // to/from frontend
    output ariane_pkg::icache_arsp_t icache_areq_o,
    // data requests
    input ariane_pkg::icache_dreq_t icache_dreq_i,  // to/from frontend
    output ariane_pkg::icache_drsp_t icache_dreq_o,
    //   }}}

    //  D$
    //  {{{
    //    Cache management
    input logic dcache_enable_i,  // from CSR
    input logic dcache_flush_i,  // high until acknowledged
    output logic                       dcache_flush_ack_o,     // send a single cycle acknowledge signal when the cache is flushed
    output logic dcache_miss_o,  // we missed on a ld/st

    //  AMO interface
    input  ariane_pkg::amo_req_t                     dcache_amo_req_i,    // from LSU
    output ariane_pkg::amo_resp_t                    dcache_amo_resp_o,   // to LSU
    //  CMO interface
    input  cmo_req_t                                 dcache_cmo_req_i,    // from CMO FU
    output cmo_rsp_t                                 dcache_cmo_resp_o,   // to CMO FU
    //  Request ports
    input  ariane_pkg::dcache_req_i_t [NumPorts-1:0] dcache_req_ports_i,  // from LSU
    output ariane_pkg::dcache_req_o_t [NumPorts-1:0] dcache_req_ports_o,  // to LSU
    //  Write Buffer status
    output logic                                     wbuffer_empty_o,
    output logic                                     wbuffer_not_ni_o,

    //  Hardware memory prefetcher configuration
    input  logic [NrHwPrefetchers-1:0]       hwpf_base_set_i,
    input  logic [NrHwPrefetchers-1:0][63:0] hwpf_base_i,
    output logic [NrHwPrefetchers-1:0][63:0] hwpf_base_o,
    input  logic [NrHwPrefetchers-1:0]       hwpf_param_set_i,
    input  logic [NrHwPrefetchers-1:0][63:0] hwpf_param_i,
    output logic [NrHwPrefetchers-1:0][63:0] hwpf_param_o,
    input  logic [NrHwPrefetchers-1:0]       hwpf_throttle_set_i,
    input  logic [NrHwPrefetchers-1:0][63:0] hwpf_throttle_i,
    output logic [NrHwPrefetchers-1:0][63:0] hwpf_throttle_o,
    output logic [               63:0]       hwpf_status_o,
    //  }}}

    //  AXI port to upstream memory/peripherals
    //  {{{
    output noc_req_t  noc_req_o,
    input  noc_resp_t noc_resp_i
    //  }}}
);
  //  }}}

  `include "axi/typedef.svh"

  //  I$ instantiation
  //  {{{
  logic icache_miss_valid, icache_miss_ready;
  wt_cache_pkg::icache_req_t icache_miss;

  logic icache_miss_resp_valid;
  wt_cache_pkg::icache_rtrn_t icache_miss_resp;

  localparam int ICACHE_RDTXID = 1 << (ariane_pkg::MEM_TID_WIDTH - 1);

  cva6_icache #(
      .CVA6Cfg(CVA6Cfg),
      .RdTxId (ICACHE_RDTXID)
  ) i_cva6_icache (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .flush_i       (icache_flush_i),
      .en_i          (icache_en_i),
      .miss_o        (icache_miss_o),
      .areq_i        (icache_areq_i),
      .areq_o        (icache_areq_o),
      .dreq_i        (icache_dreq_i),
      .dreq_o        (icache_dreq_o),
      .mem_rtrn_vld_i(icache_miss_resp_valid),
      .mem_rtrn_i    (icache_miss_resp),
      .mem_data_req_o(icache_miss_valid),
      .mem_data_ack_i(icache_miss_ready),
      .mem_data_o    (icache_miss)
  );
  //  }}}

  //  D$ instantiation
  //  {{{
  `include "hpdcache_typedef.svh"

  //    0: Page-Table Walk (PTW)
  //    1: Load unit
  //    2: Accelerator load
  //    3: Store/AMO
  //    .
  //    .
  //    .
  //    NumPorts: CMO
  //    NumPorts + 1: Hardware Memory Prefetcher (hwpf)
  localparam int HPDCACHE_NREQUESTERS = NumPorts + 2;

  typedef logic [CVA6Cfg.AxiAddrWidth-1:0] hpdcache_mem_addr_t;
  typedef logic [ariane_pkg::MEM_TID_WIDTH-1:0] hpdcache_mem_id_t;
  typedef logic [CVA6Cfg.AxiDataWidth-1:0] hpdcache_mem_data_t;
  typedef logic [CVA6Cfg.AxiDataWidth/8-1:0] hpdcache_mem_be_t;
  `HPDCACHE_TYPEDEF_MEM_REQ_T(hpdcache_mem_req_t, hpdcache_mem_addr_t, hpdcache_mem_id_t);
  `HPDCACHE_TYPEDEF_MEM_RESP_R_T(hpdcache_mem_resp_r_t, hpdcache_mem_id_t, hpdcache_mem_data_t);
  `HPDCACHE_TYPEDEF_MEM_REQ_W_T(hpdcache_mem_req_w_t, hpdcache_mem_data_t, hpdcache_mem_be_t);
  `HPDCACHE_TYPEDEF_MEM_RESP_W_T(hpdcache_mem_resp_w_t, hpdcache_mem_id_t);

  typedef logic [63:0] hwpf_stride_param_t;

  logic                        dcache_req_valid[HPDCACHE_NREQUESTERS-1:0];
  logic                        dcache_req_ready[HPDCACHE_NREQUESTERS-1:0];
  hpdcache_pkg::hpdcache_req_t dcache_req      [HPDCACHE_NREQUESTERS-1:0];
  logic                        dcache_req_abort[HPDCACHE_NREQUESTERS-1:0];
  hpdcache_pkg::hpdcache_tag_t dcache_req_tag  [HPDCACHE_NREQUESTERS-1:0];
  hpdcache_pkg::hpdcache_pma_t dcache_req_pma  [HPDCACHE_NREQUESTERS-1:0];
  logic                        dcache_rsp_valid[HPDCACHE_NREQUESTERS-1:0];
  hpdcache_pkg::hpdcache_rsp_t dcache_rsp      [HPDCACHE_NREQUESTERS-1:0];
  logic dcache_read_miss, dcache_write_miss;

  logic                                   [                2:0] snoop_valid;
  logic                                   [                2:0] snoop_abort;
  hpdcache_pkg::hpdcache_req_offset_t     [                2:0] snoop_addr_offset;
  hpdcache_pkg::hpdcache_tag_t            [                2:0] snoop_addr_tag;
  logic                                   [                2:0] snoop_phys_indexed;

  logic                                                         dcache_cmo_req_is_prefetch;

  logic                                                         dcache_miss_ready;
  logic                                                         dcache_miss_valid;
  hpdcache_mem_req_t                                            dcache_miss;

  logic                                                         dcache_miss_resp_ready;
  logic                                                         dcache_miss_resp_valid;
  hpdcache_mem_resp_r_t                                         dcache_miss_resp;

  logic                                                         dcache_wbuf_ready;
  logic                                                         dcache_wbuf_valid;
  hpdcache_mem_req_t                                            dcache_wbuf;

  logic                                                         dcache_wbuf_data_ready;
  logic                                                         dcache_wbuf_data_valid;
  hpdcache_mem_req_w_t                                          dcache_wbuf_data;

  logic                                                         dcache_wbuf_resp_ready;
  logic                                                         dcache_wbuf_resp_valid;
  hpdcache_mem_resp_w_t                                         dcache_wbuf_resp;

  logic                                                         dcache_uc_read_ready;
  logic                                                         dcache_uc_read_valid;
  hpdcache_mem_req_t                                            dcache_uc_read;

  logic                                                         dcache_uc_read_resp_ready;
  logic                                                         dcache_uc_read_resp_valid;
  hpdcache_mem_resp_r_t                                         dcache_uc_read_resp;

  logic                                                         dcache_uc_write_ready;
  logic                                                         dcache_uc_write_valid;
  hpdcache_mem_req_t                                            dcache_uc_write;

  logic                                                         dcache_uc_write_data_ready;
  logic                                                         dcache_uc_write_data_valid;
  hpdcache_mem_req_w_t                                          dcache_uc_write_data;

  logic                                                         dcache_uc_write_resp_ready;
  logic                                                         dcache_uc_write_resp_valid;
  hpdcache_mem_resp_w_t                                         dcache_uc_write_resp;

  hwpf_stride_pkg::hwpf_stride_throttle_t [NrHwPrefetchers-1:0] hwpf_throttle_in;
  hwpf_stride_pkg::hwpf_stride_throttle_t [NrHwPrefetchers-1:0] hwpf_throttle_out;

  generate
    ariane_pkg::dcache_req_i_t dcache_req_ports[HPDCACHE_NREQUESTERS-1:0];

    for (genvar r = 0; r < (NumPorts - 1); r++) begin : cva6_hpdcache_load_if_adapter_gen
      assign dcache_req_ports[r] = dcache_req_ports_i[r];

      cva6_hpdcache_if_adapter #(
          .CVA6Cfg     (CVA6Cfg),
          .is_load_port(1'b1)
      ) i_cva6_hpdcache_load_if_adapter (
          .clk_i,
          .rst_ni,

          .hpdcache_req_sid_i(hpdcache_pkg::hpdcache_req_sid_t'(r)),

          .cva6_req_i     (dcache_req_ports[r]),
          .cva6_req_o     (dcache_req_ports_o[r]),
          .cva6_amo_req_i ('0),
          .cva6_amo_resp_o(  /* unused */),

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

    cva6_hpdcache_if_adapter #(
        .CVA6Cfg     (CVA6Cfg),
        .is_load_port(1'b0)
    ) i_cva6_hpdcache_store_if_adapter (
        .clk_i,
        .rst_ni,

        .hpdcache_req_sid_i(hpdcache_pkg::hpdcache_req_sid_t'(NumPorts - 1)),

        .cva6_req_i     (dcache_req_ports_i[NumPorts-1]),
        .cva6_req_o     (dcache_req_ports_o[NumPorts-1]),
        .cva6_amo_req_i (dcache_amo_req_i),
        .cva6_amo_resp_o(dcache_amo_resp_o),

        .hpdcache_req_valid_o(dcache_req_valid[NumPorts-1]),
        .hpdcache_req_ready_i(dcache_req_ready[NumPorts-1]),
        .hpdcache_req_o      (dcache_req[NumPorts-1]),
        .hpdcache_req_abort_o(dcache_req_abort[NumPorts-1]),
        .hpdcache_req_tag_o  (dcache_req_tag[NumPorts-1]),
        .hpdcache_req_pma_o  (dcache_req_pma[NumPorts-1]),

        .hpdcache_rsp_valid_i(dcache_rsp_valid[NumPorts-1]),
        .hpdcache_rsp_i      (dcache_rsp[NumPorts-1])
    );

`ifdef HPDCACHE_ENABLE_CMO
    cva6_hpdcache_cmo_if_adapter #(
        .cmo_req_t(cmo_req_t),
        .cmo_rsp_t(cmo_rsp_t)
    ) i_cva6_hpdcache_cmo_if_adapter (
        .clk_i,
        .rst_ni,

        .dcache_req_sid_i(hpdcache_pkg::hpdcache_req_sid_t'(NumPorts)),

        .cva6_cmo_req_i (dcache_cmo_req_i),
        .cva6_cmo_resp_o(dcache_cmo_resp_o),

        .dcache_req_valid_o(dcache_req_valid[NumPorts]),
        .dcache_req_ready_i(dcache_req_ready[NumPorts]),
        .dcache_req_o      (dcache_req[NumPorts]),
        .dcache_req_abort_o(dcache_req_abort[NumPorts]),
        .dcache_req_tag_o  (dcache_req_tag[NumPorts]),
        .dcache_req_pma_o  (dcache_req_pma[NumPorts]),

        .dcache_rsp_valid_i(dcache_rsp_valid[NumPorts]),
        .dcache_rsp_i      (dcache_rsp[NumPorts])
    );
`else
    assign dcache_req_valid[NumPorts] = 1'b0,
        dcache_req[NumPorts] = '0,
        dcache_req_abort[NumPorts] = 1'b0,
        dcache_req_tag[NumPorts] = '0,
        dcache_req_pma[NumPorts] = '0;
`endif
  endgenerate

  //  Snoop load port
  assign snoop_valid[0] = dcache_req_valid[1] & dcache_req_ready[1],
      snoop_abort[0] = dcache_req_abort[1],
      snoop_addr_offset[0] = dcache_req[1].addr_offset,
      snoop_addr_tag[0] = dcache_req_tag[1],
      snoop_phys_indexed[0] = dcache_req[1].phys_indexed;

  //  Snoop Store/AMO port
  assign snoop_valid[1] = dcache_req_valid[NumPorts-1] & dcache_req_ready[NumPorts-1],
      snoop_abort[1] = dcache_req_abort[NumPorts-1],
      snoop_addr_offset[1] = dcache_req[NumPorts-1].addr_offset,
      snoop_addr_tag[1] = dcache_req_tag[NumPorts-1],
      snoop_phys_indexed[1] = dcache_req[NumPorts-1].phys_indexed;

`ifdef HPDCACHE_ENABLE_CMO
  //  Snoop CMO port (in case of read prefetch accesses)
  assign dcache_cmo_req_is_prefetch = hpdcache_pkg::is_cmo_prefetch(
      dcache_req[NumPorts].op, dcache_req[NumPorts].size
  );
  assign snoop_valid[2]        = dcache_req_valid[NumPorts]
                               & dcache_req_ready[NumPorts]
                               & dcache_cmo_req_is_prefetch,
      snoop_abort[2] = dcache_req_abort[NumPorts],
      snoop_addr_offset[2] = dcache_req[NumPorts].addr_offset,
      snoop_addr_tag[2] = dcache_req_tag[NumPorts],
      snoop_phys_indexed[2] = dcache_req[NumPorts].phys_indexed;
`else
  assign snoop_valid[2] = 1'b0,
      snoop_abort[2] = 1'b0,
      snoop_addr_offset[2] = '0,
      snoop_addr_tag[2] = '0,
      snoop_phys_indexed[2] = 1'b0;
`endif

  generate
    for (genvar h = 0; h < NrHwPrefetchers; h++) begin : hwpf_throttle_gen
      assign hwpf_throttle_in[h] = hwpf_stride_pkg::hwpf_stride_throttle_t'(hwpf_throttle_i[h]),
          hwpf_throttle_o[h] = hwpf_stride_pkg::hwpf_stride_param_t'(hwpf_throttle_out[h]);
    end
  endgenerate

  hwpf_stride_wrapper #(
      .NUM_HW_PREFETCH(NrHwPrefetchers),
      .NUM_SNOOP_PORTS(3)
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

      .hpdcache_req_sid_i(hpdcache_pkg::hpdcache_req_sid_t'(NumPorts + 1)),

      .hpdcache_req_valid_o(dcache_req_valid[NumPorts+1]),
      .hpdcache_req_ready_i(dcache_req_ready[NumPorts+1]),
      .hpdcache_req_o      (dcache_req[NumPorts+1]),
      .hpdcache_req_abort_o(dcache_req_abort[NumPorts+1]),
      .hpdcache_req_tag_o  (dcache_req_tag[NumPorts+1]),
      .hpdcache_req_pma_o  (dcache_req_pma[NumPorts+1]),
      .hpdcache_rsp_valid_i(dcache_rsp_valid[NumPorts+1]),
      .hpdcache_rsp_i      (dcache_rsp[NumPorts+1])
  );

  hpdcache #(
      .NREQUESTERS          (HPDCACHE_NREQUESTERS),
      .HPDcacheMemIdWidth   (ariane_pkg::MEM_TID_WIDTH),
      .HPDcacheMemDataWidth (CVA6Cfg.AxiDataWidth),
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

      .mem_req_miss_read_ready_i(dcache_miss_ready),
      .mem_req_miss_read_valid_o(dcache_miss_valid),
      .mem_req_miss_read_o      (dcache_miss),

      .mem_resp_miss_read_ready_o(dcache_miss_resp_ready),
      .mem_resp_miss_read_valid_i(dcache_miss_resp_valid),
      .mem_resp_miss_read_i      (dcache_miss_resp),

      .mem_req_wbuf_write_ready_i(dcache_wbuf_ready),
      .mem_req_wbuf_write_valid_o(dcache_wbuf_valid),
      .mem_req_wbuf_write_o      (dcache_wbuf),

      .mem_req_wbuf_write_data_ready_i(dcache_wbuf_data_ready),
      .mem_req_wbuf_write_data_valid_o(dcache_wbuf_data_valid),
      .mem_req_wbuf_write_data_o      (dcache_wbuf_data),

      .mem_resp_wbuf_write_ready_o(dcache_wbuf_resp_ready),
      .mem_resp_wbuf_write_valid_i(dcache_wbuf_resp_valid),
      .mem_resp_wbuf_write_i      (dcache_wbuf_resp),

      .mem_req_uc_read_ready_i(dcache_uc_read_ready),
      .mem_req_uc_read_valid_o(dcache_uc_read_valid),
      .mem_req_uc_read_o      (dcache_uc_read),

      .mem_resp_uc_read_ready_o(dcache_uc_read_resp_ready),
      .mem_resp_uc_read_valid_i(dcache_uc_read_resp_valid),
      .mem_resp_uc_read_i      (dcache_uc_read_resp),

      .mem_req_uc_write_ready_i(dcache_uc_write_ready),
      .mem_req_uc_write_valid_o(dcache_uc_write_valid),
      .mem_req_uc_write_o      (dcache_uc_write),

      .mem_req_uc_write_data_ready_i(dcache_uc_write_data_ready),
      .mem_req_uc_write_data_valid_o(dcache_uc_write_data_valid),
      .mem_req_uc_write_data_o      (dcache_uc_write_data),

      .mem_resp_uc_write_ready_o(dcache_uc_write_resp_ready),
      .mem_resp_uc_write_valid_i(dcache_uc_write_resp_valid),
      .mem_resp_uc_write_i      (dcache_uc_write_resp),

      .evt_cache_write_miss_o(dcache_write_miss),
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

      .wbuf_empty_o(wbuffer_empty_o),

      .cfg_enable_i                       (dcache_enable_i),
      .cfg_wbuf_threshold_i               (4'd2),
      .cfg_wbuf_reset_timecnt_on_write_i  (1'b1),
      .cfg_wbuf_sequential_waw_i          (1'b0),
      .cfg_wbuf_inhibit_write_coalescing_i(1'b0),
      .cfg_prefetch_updt_plru_i           (1'b1),
      .cfg_error_on_cacheable_amo_i       (1'b0),
      .cfg_rtab_single_entry_i            (1'b0)
  );

  assign dcache_miss_o = dcache_read_miss, wbuffer_not_ni_o = wbuffer_empty_o;

  always_ff @(posedge clk_i or negedge rst_ni) begin : dcache_flush_ff
    if (!rst_ni) dcache_flush_ack_o <= 1'b0;
    else dcache_flush_ack_o <= ~dcache_flush_ack_o & dcache_flush_i;
  end

  //  }}}

  //  AXI arbiter instantiation
  //  {{{
  typedef logic [CVA6Cfg.AxiAddrWidth-1:0] axi_addr_t;
  typedef logic [CVA6Cfg.AxiDataWidth-1:0] axi_data_t;
  typedef logic [CVA6Cfg.AxiDataWidth/8-1:0] axi_strb_t;
  typedef logic [CVA6Cfg.AxiIdWidth-1:0] axi_id_t;
  typedef logic [CVA6Cfg.AxiUserWidth-1:0] axi_user_t;
  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_chan_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_b_chan_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_chan_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_r_chan_t, axi_data_t, axi_id_t, axi_user_t)

  cva6_hpdcache_subsystem_axi_arbiter #(
      .HPDcacheMemIdWidth   (ariane_pkg::MEM_TID_WIDTH),
      .HPDcacheMemDataWidth (CVA6Cfg.AxiDataWidth),
      .hpdcache_mem_req_t   (hpdcache_mem_req_t),
      .hpdcache_mem_req_w_t (hpdcache_mem_req_w_t),
      .hpdcache_mem_resp_r_t(hpdcache_mem_resp_r_t),
      .hpdcache_mem_resp_w_t(hpdcache_mem_resp_w_t),

      .AxiAddrWidth (CVA6Cfg.AxiAddrWidth),
      .AxiDataWidth (CVA6Cfg.AxiDataWidth),
      .AxiIdWidth   (CVA6Cfg.AxiIdWidth),
      .AxiUserWidth (CVA6Cfg.AxiUserWidth),
      .axi_ar_chan_t(axi_ar_chan_t),
      .axi_aw_chan_t(axi_aw_chan_t),
      .axi_w_chan_t (axi_w_chan_t),
      .axi_req_t    (noc_req_t),
      .axi_rsp_t    (noc_resp_t)
  ) i_axi_arbiter (
      .clk_i,
      .rst_ni,

      .icache_miss_valid_i(icache_miss_valid),
      .icache_miss_ready_o(icache_miss_ready),
      .icache_miss_i      (icache_miss),
      .icache_miss_id_i   (hpdcache_mem_id_t'(ICACHE_RDTXID)),

      .icache_miss_resp_valid_o(icache_miss_resp_valid),
      .icache_miss_resp_o      (icache_miss_resp),

      .dcache_miss_ready_o(dcache_miss_ready),
      .dcache_miss_valid_i(dcache_miss_valid),
      .dcache_miss_i      (dcache_miss),

      .dcache_miss_resp_ready_i(dcache_miss_resp_ready),
      .dcache_miss_resp_valid_o(dcache_miss_resp_valid),
      .dcache_miss_resp_o      (dcache_miss_resp),

      .dcache_wbuf_ready_o(dcache_wbuf_ready),
      .dcache_wbuf_valid_i(dcache_wbuf_valid),
      .dcache_wbuf_i      (dcache_wbuf),

      .dcache_wbuf_data_ready_o(dcache_wbuf_data_ready),
      .dcache_wbuf_data_valid_i(dcache_wbuf_data_valid),
      .dcache_wbuf_data_i      (dcache_wbuf_data),

      .dcache_wbuf_resp_ready_i(dcache_wbuf_resp_ready),
      .dcache_wbuf_resp_valid_o(dcache_wbuf_resp_valid),
      .dcache_wbuf_resp_o      (dcache_wbuf_resp),

      .dcache_uc_read_ready_o(dcache_uc_read_ready),
      .dcache_uc_read_valid_i(dcache_uc_read_valid),
      .dcache_uc_read_i      (dcache_uc_read),
      .dcache_uc_read_id_i   ('1),

      .dcache_uc_read_resp_ready_i(dcache_uc_read_resp_ready),
      .dcache_uc_read_resp_valid_o(dcache_uc_read_resp_valid),
      .dcache_uc_read_resp_o      (dcache_uc_read_resp),

      .dcache_uc_write_ready_o(dcache_uc_write_ready),
      .dcache_uc_write_valid_i(dcache_uc_write_valid),
      .dcache_uc_write_i      (dcache_uc_write),
      .dcache_uc_write_id_i   ('1),

      .dcache_uc_write_data_ready_o(dcache_uc_write_data_ready),
      .dcache_uc_write_data_valid_i(dcache_uc_write_data_valid),
      .dcache_uc_write_data_i      (dcache_uc_write_data),

      .dcache_uc_write_resp_ready_i(dcache_uc_write_resp_ready),
      .dcache_uc_write_resp_valid_o(dcache_uc_write_resp_valid),
      .dcache_uc_write_resp_o      (dcache_uc_write_resp),

      .axi_req_o (noc_req_o),
      .axi_resp_i(noc_resp_i)
  );
  //  }}}

  //  Assertions
  //  {{{
  //  pragma translate_off
  initial
    assert (hpdcache_pkg::HPDCACHE_REQ_SRC_ID_WIDTH >= $clog2(HPDCACHE_NREQUESTERS))
    else $fatal(1, "HPDCACHE_REQ_SRC_ID_WIDTH is not wide enough");

  a_invalid_instruction_fetch :
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) icache_dreq_o.valid |-> (|icache_dreq_o.data) !== 1'hX)
  else
    $warning(
        1,
        "[l1 dcache] reading invalid instructions: vaddr=%08X, data=%08X",
        icache_dreq_o.vaddr,
        icache_dreq_o.data
    );

  a_invalid_write_data :
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) dcache_req_ports_i[2].data_req |-> |dcache_req_ports_i[2].data_be |-> (|dcache_req_ports_i[2].data_wdata) !== 1'hX)
  else
    $warning(
        1,
        "[l1 dcache] writing invalid data: paddr=%016X, be=%02X, data=%016X",
        {
          dcache_req_ports_i[2].address_tag, dcache_req_ports_i[2].address_index
        },
        dcache_req_ports_i[2].data_be,
        dcache_req_ports_i[2].data_wdata
    );

  for (genvar j = 0; j < 2; j++) begin : gen_assertion
    a_invalid_read_data :
    assert property (
      @(posedge clk_i) disable iff (!rst_ni) dcache_req_ports_o[j].data_rvalid && ~dcache_req_ports_i[j].kill_req |-> (|dcache_req_ports_o[j].data_rdata) !== 1'hX)
    else
      $warning(
          1,
          "[l1 dcache] reading invalid data on port %01d: data=%016X",
          j,
          dcache_req_ports_o[j].data_rdata
      );
  end
  //  pragma translate_on
  //  }}}

endmodule : cva6_hpdcache_subsystem
