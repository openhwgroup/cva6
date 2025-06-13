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

`include "axi_types.svh"


module cva6_hpdcache_subsystem
//  Parameters
//  {{{
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type ypb_fetch_req_t = logic,
    parameter type ypb_fetch_rsp_t = logic,
    parameter type ypb_store_req_t = logic,
    parameter type ypb_store_rsp_t = logic,
    parameter type ypb_amo_req_t = logic,
    parameter type ypb_amo_rsp_t = logic,
    parameter type ypb_load_req_t = logic,
    parameter type ypb_load_rsp_t = logic,
    parameter type ypb_mmu_ptw_req_t = logic,
    parameter type ypb_mmu_ptw_rsp_t = logic,
    parameter type ypb_zcmt_req_t = logic,
    parameter type ypb_zcmt_rsp_t = logic,

    parameter int NrHwPrefetchers = 4,

    parameter type noc_req_t  = logic,
    parameter type noc_resp_t = logic,

    parameter type cmo_req_t = logic,
    parameter type cmo_rsp_t = logic
)
//  }}}

//  Ports
//  {{{
(

    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,

    //  AXI port to upstream memory/peripherals
    //  {{{
    // noc request, can be AXI or OpenPiton - SUBSYSTEM
    output noc_req_t  noc_req_o,
    // noc response, can be AXI or OpenPiton - SUBSYSTEM
    input  noc_resp_t noc_resp_i,
    //  }}}

    //  I$
    //  {{{
    // Instruction cache enable - CSR_REGFILE
    input logic icache_en_i,
    // Flush the instruction cache - CONTROLLER
    input logic icache_flush_i,
    // instructino cache miss - PERF_COUNTERS
    output logic icache_miss_o,
    // Fetch Request channel - FRONTEND
    input ypb_fetch_req_t ypb_fetch_req_i,
    // Fetch Response channel - FRONTEND
    output ypb_fetch_rsp_t ypb_fetch_rsp_o,
    //   }}}

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

    // CMO interface request - TO_BE_COMPLETED
    input  cmo_req_t dcache_cmo_req_i,
    // CMO interface response - TO_BE_COMPLETED
    output cmo_rsp_t dcache_cmo_rsp_o,

    // Store cache response - CACHES
    input ypb_store_req_t ypb_store_req_i,
    // Store cache request - CACHES
    output ypb_store_rsp_t ypb_store_rsp_o,
    // AMO cache request - CACHES
    input ypb_amo_req_t ypb_amo_req_i,
    // AMO cache response - CACHES
    output ypb_amo_rsp_t ypb_amo_rsp_o,
    // Load cache request - CACHES
    input ypb_load_req_t ypb_load_req_i,
    // Load cache response - CACHES
    output ypb_load_rsp_t ypb_load_rsp_o,
    // MMU Ptw cache request - CACHES
    input ypb_mmu_ptw_req_t ypb_mmu_ptw_req_i,
    // MMU Ptw cache response - CACHES
    output ypb_mmu_ptw_rsp_t ypb_mmu_ptw_rsp_o,
    // Zcmt cache response - CACHES
    input ypb_zcmt_req_t ypb_zcmt_req_i,
    // Zcmt cache response - CACHES
    output ypb_zcmt_rsp_t ypb_zcmt_rsp_o,

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
    output logic [               63:0]       hwpf_status_o
    //  }}}
);
  //  }}}

  localparam type axi_ar_chan_t = `AXI_AR_CHAN_T(CVA6Cfg);
  localparam type axi_aw_chan_t = `AXI_AW_CHAN_T(CVA6Cfg);
  localparam type axi_w_chan_t = `AXI_W_CHAN_T(CVA6Cfg);
  localparam type axi_b_chan_t = `AXI_B_CHAN_T(CVA6Cfg);
  localparam type axi_r_chan_t = `AXI_R_CHAN_T(CVA6Cfg);

  localparam type icache_req_t = struct packed {
    logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] way;  // way to replace
    logic [CVA6Cfg.PLEN-1:0] paddr;  // physical address
    logic nc;  // noncacheable
    logic [CVA6Cfg.MEM_TID_WIDTH-1:0] tid;  // threadi id (used as transaction id in Ariane)
  };
  localparam type icache_rtrn_t = struct packed {
    wt_cache_pkg::icache_in_t rtype;  // see definitions above
    logic [CVA6Cfg.ICACHE_LINE_WIDTH-1:0] data;  // full cache line width
    logic [CVA6Cfg.ICACHE_USER_LINE_WIDTH-1:0] user;  // user bits
    struct packed {
      logic                                      vld;  // invalidate only affected way
      logic                                      all;  // invalidate all ways
      logic [CVA6Cfg.ICACHE_INDEX_WIDTH-1:0]     idx;  // physical address to invalidate
      logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] way;  // way to invalidate
    } inv;  // invalidation vector
    logic [CVA6Cfg.MEM_TID_WIDTH-1:0] tid;  // threadi id (used as transaction id in Ariane)
  };

  function int unsigned __minu(int unsigned x, int unsigned y);
    return x < y ? x : y;
  endfunction

  function int unsigned __maxu(int unsigned x, int unsigned y);
    return y < x ? x : y;
  endfunction

  //  I$ instantiation
  //  {{{
  logic icache_miss_valid, icache_miss_ready;
  icache_req_t icache_miss;

  logic icache_miss_resp_valid;
  icache_rtrn_t icache_miss_resp;

  localparam int ICACHE_RDTXID = 1 << (CVA6Cfg.MEM_TID_WIDTH - 1);

  cva6_icache #(
      .CVA6Cfg(CVA6Cfg),
      .ypb_fetch_req_t(ypb_fetch_req_t),
      .ypb_fetch_rsp_t(ypb_fetch_rsp_t),
      .icache_req_t(icache_req_t),
      .icache_rtrn_t(icache_rtrn_t),
      .RdTxId(ICACHE_RDTXID)
  ) i_cva6_icache (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .flush_i        (icache_flush_i),
      .en_i           (icache_en_i),
      .miss_o         (icache_miss_o),
      .ypb_fetch_req_i(ypb_fetch_req_i),
      .ypb_fetch_rsp_o(ypb_fetch_rsp_o),
      .mem_rtrn_vld_i (icache_miss_resp_valid),
      .mem_rtrn_i     (icache_miss_resp),
      .mem_data_req_o (icache_miss_valid),
      .mem_data_ack_i (icache_miss_ready),
      .mem_data_o     (icache_miss)
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
  localparam int HPDCACHE_ENABLE_CMO = 0;
  localparam int HPDCACHE_NREQUESTERS = 3 + (HPDCACHE_ENABLE_CMO ? 1:0) + (CVA6Cfg.MmuPresent ? 1:0) + (CVA6Cfg.RVZCMT ? 1:0);
  localparam int NUM_SNOOP_PORTS = HPDCACHE_ENABLE_CMO ? 3 : 2;

  localparam int MMU_PTW_INDEX = 0;
  localparam int ZCMT_INDEX = (CVA6Cfg.RVZCMT ? 1 : 0);
  localparam int LOAD_INDEX = (CVA6Cfg.MmuPresent ? ZCMT_INDEX + 1 : ZCMT_INDEX);
  localparam int STORE_AMO_INDEX = LOAD_INDEX + 1;
  localparam int CMO_INDEX = STORE_AMO_INDEX + 1;
  localparam int HWPF_INDEX = (HPDCACHE_ENABLE_CMO ? CMO_INDEX + 1 : CMO_INDEX);

  function automatic hpdcache_pkg::hpdcache_user_cfg_t hpdcacheSetConfig();
    hpdcache_pkg::hpdcache_user_cfg_t userCfg;
    userCfg.nRequesters = HPDCACHE_NREQUESTERS;
    userCfg.paWidth = CVA6Cfg.PLEN;
    userCfg.wordWidth = CVA6Cfg.XLEN;
    userCfg.sets = CVA6Cfg.DCACHE_NUM_WORDS;
    userCfg.ways = CVA6Cfg.DCACHE_SET_ASSOC;
    userCfg.clWords = CVA6Cfg.DCACHE_LINE_WIDTH / CVA6Cfg.XLEN;
    userCfg.reqWords = 1;
    userCfg.reqTransIdWidth = CVA6Cfg.DcacheIdWidth;
    userCfg.reqSrcIdWidth = 3;  // Up to 8 requesters
    userCfg.victimSel = hpdcache_pkg::HPDCACHE_VICTIM_RANDOM;
    userCfg.dataWaysPerRamWord = __minu(CVA6Cfg.DCACHE_SET_ASSOC, 128 / CVA6Cfg.XLEN);
    userCfg.dataSetsPerRam = CVA6Cfg.DCACHE_NUM_WORDS;
    userCfg.dataRamByteEnable = 1'b1;
    userCfg.accessWords = __maxu(CVA6Cfg.AxiDataWidth / CVA6Cfg.XLEN, 1  /*reqWords*/);
    userCfg.mshrSets = CVA6Cfg.NrLoadBufEntries < 16 ? 1 : CVA6Cfg.NrLoadBufEntries / 2;
    userCfg.mshrWays = CVA6Cfg.NrLoadBufEntries < 16 ? CVA6Cfg.NrLoadBufEntries : 2;
    userCfg.mshrWaysPerRamWord = CVA6Cfg.NrLoadBufEntries < 16 ? CVA6Cfg.NrLoadBufEntries : 2;
    userCfg.mshrSetsPerRam = CVA6Cfg.NrLoadBufEntries < 16 ? 1 : CVA6Cfg.NrLoadBufEntries / 2;
    userCfg.mshrRamByteEnable = 1'b1;
    userCfg.mshrUseRegbank = (CVA6Cfg.NrLoadBufEntries < 16);
    userCfg.refillCoreRspFeedthrough = 1'b1;
    userCfg.refillFifoDepth = 2;
    userCfg.wbufDirEntries = CVA6Cfg.WtDcacheWbufDepth;
    userCfg.wbufDataEntries = CVA6Cfg.WtDcacheWbufDepth;
    userCfg.wbufWords = 1;
    userCfg.wbufTimecntWidth = 3;
    userCfg.rtabEntries = 4;
    /*FIXME we should add additional CVA6 config parameters (flushEntries)*/
    userCfg.flushEntries = CVA6Cfg.WtDcacheWbufDepth;
    /*FIXME we should add additional CVA6 config parameters (flushFifoDepth)*/
    userCfg.flushFifoDepth = CVA6Cfg.WtDcacheWbufDepth;
    userCfg.memAddrWidth = CVA6Cfg.AxiAddrWidth;
    userCfg.memIdWidth = CVA6Cfg.MEM_TID_WIDTH;
    userCfg.memDataWidth = CVA6Cfg.AxiDataWidth;
    userCfg.wtEn =
        (CVA6Cfg.DCacheType == config_pkg::HPDCACHE_WT) ||
        (CVA6Cfg.DCacheType == config_pkg::HPDCACHE_WT_WB);
    userCfg.wbEn =
        (CVA6Cfg.DCacheType == config_pkg::HPDCACHE_WB) ||
        (CVA6Cfg.DCacheType == config_pkg::HPDCACHE_WT_WB);
    return userCfg;
  endfunction

  localparam hpdcache_pkg::hpdcache_user_cfg_t HPDcacheUserCfg = hpdcacheSetConfig();
  localparam hpdcache_pkg::hpdcache_cfg_t HPDcacheCfg = hpdcache_pkg::hpdcacheBuildConfig(
      HPDcacheUserCfg
  );

  `HPDCACHE_TYPEDEF_MEM_ATTR_T(hpdcache_mem_addr_t, hpdcache_mem_id_t, hpdcache_mem_data_t,
                               hpdcache_mem_be_t, HPDcacheCfg);
  `HPDCACHE_TYPEDEF_MEM_REQ_T(hpdcache_mem_req_t, hpdcache_mem_addr_t, hpdcache_mem_id_t);
  `HPDCACHE_TYPEDEF_MEM_RESP_R_T(hpdcache_mem_resp_r_t, hpdcache_mem_id_t, hpdcache_mem_data_t);
  `HPDCACHE_TYPEDEF_MEM_REQ_W_T(hpdcache_mem_req_w_t, hpdcache_mem_data_t, hpdcache_mem_be_t);
  `HPDCACHE_TYPEDEF_MEM_RESP_W_T(hpdcache_mem_resp_w_t, hpdcache_mem_id_t);

  `HPDCACHE_TYPEDEF_REQ_ATTR_T(hpdcache_req_offset_t, hpdcache_data_word_t, hpdcache_data_be_t,
                               hpdcache_req_data_t, hpdcache_req_be_t, hpdcache_req_sid_t,
                               hpdcache_req_tid_t, hpdcache_tag_t, HPDcacheCfg);
  `HPDCACHE_TYPEDEF_REQ_T(hpdcache_req_t, hpdcache_req_offset_t, hpdcache_req_data_t,
                          hpdcache_req_be_t, hpdcache_req_sid_t, hpdcache_req_tid_t,
                          hpdcache_tag_t);
  `HPDCACHE_TYPEDEF_RSP_T(hpdcache_rsp_t, hpdcache_req_data_t, hpdcache_req_sid_t,
                          hpdcache_req_tid_t);

  typedef logic [HPDcacheCfg.u.wbufTimecntWidth-1:0] hpdcache_wbuf_timecnt_t;

  logic                 dcache_read_ready;
  logic                 dcache_read_valid;
  hpdcache_mem_req_t    dcache_read;

  logic                 dcache_read_resp_ready;
  logic                 dcache_read_resp_valid;
  hpdcache_mem_resp_r_t dcache_read_resp;

  logic                 dcache_write_ready;
  logic                 dcache_write_valid;
  hpdcache_mem_req_t    dcache_write;

  logic                 dcache_write_data_ready;
  logic                 dcache_write_data_valid;
  hpdcache_mem_req_w_t  dcache_write_data;

  logic                 dcache_write_resp_ready;
  logic                 dcache_write_resp_valid;
  hpdcache_mem_resp_w_t dcache_write_resp;

  cva6_hpdcache_wrapper #(
      .CVA6Cfg          (CVA6Cfg),
      .HPDcacheCfg      (HPDcacheCfg),
      .ypb_store_req_t  (ypb_store_req_t),
      .ypb_store_rsp_t  (ypb_store_rsp_t),
      .ypb_amo_req_t    (ypb_amo_req_t),
      .ypb_amo_rsp_t    (ypb_amo_rsp_t),
      .ypb_load_req_t   (ypb_load_req_t),
      .ypb_load_rsp_t   (ypb_load_rsp_t),
      .ypb_mmu_ptw_req_t(ypb_mmu_ptw_req_t),
      .ypb_mmu_ptw_rsp_t(ypb_mmu_ptw_rsp_t),
      .ypb_zcmt_req_t   (ypb_zcmt_req_t),
      .ypb_zcmt_rsp_t   (ypb_zcmt_rsp_t),

      .HPDCACHE_ENABLE_CMO (HPDCACHE_ENABLE_CMO),
      .HPDCACHE_NREQUESTERS(HPDCACHE_NREQUESTERS),
      .NUM_SNOOP_PORTS     (NUM_SNOOP_PORTS),
      .MMU_PTW_INDEX       (MMU_PTW_INDEX),
      .ZCMT_INDEX          (ZCMT_INDEX),
      .LOAD_INDEX          (LOAD_INDEX),
      .STORE_AMO_INDEX     (STORE_AMO_INDEX),
      .CMO_INDEX           (CMO_INDEX),
      .HWPF_INDEX          (HWPF_INDEX),

      .NrHwPrefetchers        (NrHwPrefetchers),
      .cmo_req_t              (cmo_req_t),
      .cmo_rsp_t              (cmo_rsp_t),
      .hpdcache_mem_addr_t    (hpdcache_mem_addr_t),
      .hpdcache_mem_id_t      (hpdcache_mem_id_t),
      .hpdcache_mem_data_t    (hpdcache_mem_data_t),
      .hpdcache_mem_be_t      (hpdcache_mem_be_t),
      .hpdcache_mem_req_t     (hpdcache_mem_req_t),
      .hpdcache_mem_req_w_t   (hpdcache_mem_req_w_t),
      .hpdcache_mem_resp_r_t  (hpdcache_mem_resp_r_t),
      .hpdcache_mem_resp_w_t  (hpdcache_mem_resp_w_t),
      .hpdcache_req_offset_t  (hpdcache_req_offset_t),
      .hpdcache_data_word_t   (hpdcache_data_word_t),
      .hpdcache_req_data_t    (hpdcache_req_data_t),
      .hpdcache_req_be_t      (hpdcache_req_be_t),
      .hpdcache_req_sid_t     (hpdcache_req_sid_t),
      .hpdcache_req_tid_t     (hpdcache_req_tid_t),
      .hpdcache_tag_t         (hpdcache_tag_t),
      .hpdcache_req_t         (hpdcache_req_t),
      .hpdcache_rsp_t         (hpdcache_rsp_t),
      .hpdcache_wbuf_timecnt_t(hpdcache_wbuf_timecnt_t),
      .hpdcache_data_be_t     (hpdcache_data_be_t)
  ) i_dcache (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .dcache_enable_i(dcache_enable_i),
      .dcache_flush_i(dcache_flush_i),
      .dcache_flush_ack_o(dcache_flush_ack_o),
      .dcache_miss_o(dcache_miss_o),
      .dcache_cmo_req_i(dcache_cmo_req_i),
      .dcache_cmo_rsp_o(dcache_cmo_rsp_o),
      .ypb_store_req_i(ypb_store_req_i),
      .ypb_store_rsp_o(ypb_store_rsp_o),
      .ypb_amo_req_i(ypb_amo_req_i),
      .ypb_amo_rsp_o(ypb_amo_rsp_o),
      .ypb_load_req_i(ypb_load_req_i),
      .ypb_load_rsp_o(ypb_load_rsp_o),
      .ypb_mmu_ptw_req_i(ypb_mmu_ptw_req_i),
      .ypb_mmu_ptw_rsp_o(ypb_mmu_ptw_rsp_o),
      .ypb_zcmt_req_i(ypb_zcmt_req_i),
      .ypb_zcmt_rsp_o(ypb_zcmt_rsp_o),
      .wbuffer_empty_o(wbuffer_empty_o),
      .wbuffer_not_ni_o(wbuffer_not_ni_o),
      .hwpf_base_set_i(hwpf_base_set_i),
      .hwpf_base_i(hwpf_base_i),
      .hwpf_base_o(hwpf_base_o),
      .hwpf_param_set_i(hwpf_param_set_i),
      .hwpf_param_i(hwpf_param_i),
      .hwpf_param_o(hwpf_param_o),
      .hwpf_throttle_set_i(hwpf_throttle_set_i),
      .hwpf_throttle_i(hwpf_throttle_i),
      .hwpf_throttle_o(hwpf_throttle_o),
      .hwpf_status_o(hwpf_status_o),

      .dcache_mem_req_read_ready_i(dcache_read_ready),
      .dcache_mem_req_read_valid_o(dcache_read_valid),
      .dcache_mem_req_read_o(dcache_read),

      .dcache_mem_resp_read_ready_o(dcache_read_resp_ready),
      .dcache_mem_resp_read_valid_i(dcache_read_resp_valid),
      .dcache_mem_resp_read_i(dcache_read_resp),

      .dcache_mem_req_write_ready_i(dcache_write_ready),
      .dcache_mem_req_write_valid_o(dcache_write_valid),
      .dcache_mem_req_write_o(dcache_write),

      .dcache_mem_req_write_data_ready_i(dcache_write_data_ready),
      .dcache_mem_req_write_data_valid_o(dcache_write_data_valid),
      .dcache_mem_req_write_data_o(dcache_write_data),

      .dcache_mem_resp_write_ready_o(dcache_write_resp_ready),
      .dcache_mem_resp_write_valid_i(dcache_write_resp_valid),
      .dcache_mem_resp_write_i(dcache_write_resp)
  );

  //  AXI arbiter instantiation
  //  {{{
  cva6_hpdcache_subsystem_axi_arbiter #(
      .CVA6Cfg              (CVA6Cfg),
      .hpdcache_mem_id_t    (hpdcache_mem_id_t),
      .hpdcache_mem_req_t   (hpdcache_mem_req_t),
      .hpdcache_mem_req_w_t (hpdcache_mem_req_w_t),
      .hpdcache_mem_resp_r_t(hpdcache_mem_resp_r_t),
      .hpdcache_mem_resp_w_t(hpdcache_mem_resp_w_t),
      .icache_req_t         (icache_req_t),
      .icache_rtrn_t        (icache_rtrn_t),

      .AxiAddrWidth (CVA6Cfg.AxiAddrWidth),
      .AxiDataWidth (CVA6Cfg.AxiDataWidth),
      .AxiIdWidth   (CVA6Cfg.AxiIdWidth),
      .AxiUserWidth (CVA6Cfg.AxiUserWidth),
      .axi_ar_chan_t(axi_ar_chan_t),
      .axi_aw_chan_t(axi_aw_chan_t),
      .axi_w_chan_t (axi_w_chan_t),
      .axi_b_chan_t (axi_b_chan_t),
      .axi_r_chan_t (axi_r_chan_t),
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

      .dcache_read_ready_o(dcache_read_ready),
      .dcache_read_valid_i(dcache_read_valid),
      .dcache_read_i      (dcache_read),

      .dcache_read_resp_ready_i(dcache_read_resp_ready),
      .dcache_read_resp_valid_o(dcache_read_resp_valid),
      .dcache_read_resp_o      (dcache_read_resp),

      .dcache_write_ready_o(dcache_write_ready),
      .dcache_write_valid_i(dcache_write_valid),
      .dcache_write_i      (dcache_write),

      .dcache_write_data_ready_o(dcache_write_data_ready),
      .dcache_write_data_valid_i(dcache_write_data_valid),
      .dcache_write_data_i      (dcache_write_data),

      .dcache_write_resp_ready_i(dcache_write_resp_ready),
      .dcache_write_resp_valid_o(dcache_write_resp_valid),
      .dcache_write_resp_o      (dcache_write_resp),

      .axi_req_o (noc_req_o),
      .axi_resp_i(noc_resp_i)
  );
  //  }}}

  //  Assertions
  //  {{{
  //  pragma translate_off
  initial begin : initial_assertions
    assert (HPDcacheCfg.u.reqSrcIdWidth >= $clog2(HPDcacheCfg.u.nRequesters))
    else $fatal(1, "HPDCACHE_REQ_SRC_ID_WIDTH is not wide enough");
    assert (CVA6Cfg.MEM_TID_WIDTH <= CVA6Cfg.AxiIdWidth)
    else $fatal(1, "MEM_TID_WIDTH shall be less or equal to the AxiIdWidth");
    assert (CVA6Cfg.MEM_TID_WIDTH >= ($clog2(HPDcacheCfg.u.mshrSets * HPDcacheCfg.u.mshrWays) + 1))
    else $fatal(1, "MEM_TID_WIDTH shall allow to uniquely identify all D$ and I$ miss requests ");
    assert (CVA6Cfg.MEM_TID_WIDTH >= ($clog2(HPDcacheCfg.u.wbufDirEntries) + 1))
    else $fatal(1, "MEM_TID_WIDTH shall allow to uniquely identify all D$ write requests ");
  end

  a_invalid_instruction_fetch :
  assert property (
    @(posedge clk_i) disable iff (~rst_ni) (ypb_fetch_rsp_o.rvalid && ypb_fetch_req_i.rready) |-> (|ypb_fetch_rsp_o.r.rdata) !== 1'hX)
  else
    $warning(
        1, "[l1 icache] FETCH reading invalid instructions: data=%08X", ypb_fetch_rsp_o.r.rdata
    );

  a_invalid_read_amo :
  assert property (
    @(posedge clk_i) disable iff (~rst_ni) (ypb_amo_rsp_o.rvalid && ypb_amo_req_i.rready) |-> (|ypb_amo_rsp_o.r.rdata) !== 1'hX)
  else $warning(1, "[l1 dcache] AMO reading invalid data: data=%08X", ypb_amo_rsp_o.r.rdata);

  a_invalid_read_load :
  assert property (
    @(posedge clk_i) disable iff (~rst_ni) (ypb_load_rsp_o.rvalid && ypb_load_req_i.rready) |-> (|ypb_load_rsp_o.r.rdata) !== 1'hX)
  else $warning(1, "[l1 dcache] LOAD reading invalid data: data=%08X", ypb_amo_rsp_o.r.rdata);

  //  a_invalid_read_mmu_ptw :
  //  assert property (
  //    @(posedge clk_i) disable iff (~rst_ni) (ypb_mmu_ptw_rsp_o.rvalid && !ypb_mmu_ptw_rsp_o.invalid_data) |-> (|ypb_mmu_ptw_rsp_o.r.rdata) !== 1'hX)
  //  else
  //    $warning(
  //        1,
  //        "[l1 dcache] MMU PTW reading invalid data: data=%08X",
  //        ypb_mmu_ptw_rsp_o.r.rdata
  //    );

  //  a_invalid_read_zcmt :
  //  assert property (
  //    @(posedge clk_i) disable iff (~rst_ni) (ypb_zcmt_rsp_o.rvalid && !ypb_zcmt_rsp_o.invalid_data) |-> (|ypb_zcmt_rsp_o.r.rdata) !== 1'hX)
  //  else
  //    $warning(
  //        1,
  //        "[l1 dcache] ZCMT reading invalid data: data=%08X",
  //        ypb_zcmt_rsp_o.r.rdata
  //    );

  a_invalid_write_store :
  assert property (
    @(posedge clk_i) disable iff (~rst_ni) (ypb_store_req_i.req && ypb_store_rsp_o.gnt) |-> (|ypb_store_req_i.a.wdata) !== 1'hX)
  else
    $warning(
        1,
        "[l1 dcache] STORE writing invalid data: paddr=%016X, be=%02X, data=%016X",
        ypb_store_req_i.a.addr,
        ypb_store_req_i.a.be,
        ypb_store_req_i.a.wdata
    );

  a_invalid_write_amo :
  assert property (
    @(posedge clk_i) disable iff (~rst_ni) (ypb_amo_req_i.req && ypb_amo_rsp_o.gnt) |-> (|ypb_amo_req_i.a.wdata) !== 1'hX)
  else
    $warning(
        1,
        "[l1 dcache] AMO writing invalid data: paddr=%016X, be=%02X, data=%016X",
        ypb_amo_req_i.a.addr,
        ypb_amo_req_i.a.be,
        ypb_amo_req_i.a.wdata
    );

  //  pragma translate_on
  //  }}}

endmodule : cva6_hpdcache_subsystem
