// Copyright 2017-2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 19.03.2017
// Description: CVA6 Top-level module

`include "rvfi_types.svh"
`include "cvxif_types.svh"
`include "ypb_types.svh"

module cva6
  import ariane_pkg::*;
#(
    // CVA6 config
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,

    // RVFI PROBES
    parameter type rvfi_probes_t = logic,

    // NOC Types AXI bus or several OBI bus
    parameter type noc_req_t  = logic,
    parameter type noc_resp_t = logic,

    // CVXIF Types
    localparam type readregflags_t = `READREGFLAGS_T(CVA6Cfg),
    localparam type writeregflags_t = `WRITEREGFLAGS_T(CVA6Cfg),
    localparam type id_t = `ID_T(CVA6Cfg),
    localparam type hartid_t = `HARTID_T(CVA6Cfg),
    localparam type x_compressed_req_t = `X_COMPRESSED_REQ_T(CVA6Cfg, hartid_t),
    localparam type x_compressed_resp_t = `X_COMPRESSED_RESP_T(CVA6Cfg),
    localparam type x_issue_req_t = `X_ISSUE_REQ_T(CVA6Cfg, hartit_t, id_t),
    localparam type x_issue_resp_t = `X_ISSUE_RESP_T(CVA6Cfg, writeregflags_t, readregflags_t),
    localparam type x_register_t = `X_REGISTER_T(CVA6Cfg, hartid_t, id_t, readregflags_t),
    localparam type x_commit_t = `X_COMMIT_T(CVA6Cfg, hartid_t, id_t),
    localparam type x_result_t = `X_RESULT_T(CVA6Cfg, hartid_t, id_t, writeregflags_t),
    localparam type cvxif_req_t =
    `CVXIF_REQ_T(CVA6Cfg, x_compressed_req_t, x_issue_req_t, x_register_req_t, x_commit_t),
    localparam type cvxif_resp_t =
    `CVXIF_RESP_T(CVA6Cfg, x_compressed_resp_t, x_issue_resp_t, x_result_t)
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // Reset boot address - SUBSYSTEM
    input logic [CVA6Cfg.VLEN-1:0] boot_addr_i,
    // Hard ID reflected as CSR - SUBSYSTEM
    input logic [CVA6Cfg.XLEN-1:0] hart_id_i,
    // Level sensitive (async) interrupts - SUBSYSTEM
    input logic [1:0] irq_i,
    // Inter-processor (async) interrupt - SUBSYSTEM
    input logic ipi_i,
    // Timer (async) interrupt - SUBSYSTEM
    input logic time_irq_i,
    // Debug (async) request - SUBSYSTEM
    input logic debug_req_i,
    // Probes to build RVFI, can be left open when not used - RVFI
    output rvfi_probes_t rvfi_probes_o,
    // CVXIF request - SUBSYSTEM
    output cvxif_req_t cvxif_req_o,
    // CVXIF response - SUBSYSTEM
    input cvxif_resp_t cvxif_resp_i,
    // noc request, can be AXI or OpenPiton - SUBSYSTEM
    output noc_req_t noc_req_o,
    // noc response, can be AXI or OpenPiton - SUBSYSTEM
    input noc_resp_t noc_resp_i
);


  localparam type ypb_fetch_req_t = `YPB_REQ_T(CVA6Cfg, CVA6Cfg.FETCH_WIDTH);
  localparam type ypb_fetch_rsp_t = `YPB_RSP_T(CVA6Cfg, CVA6Cfg.FETCH_WIDTH);
  localparam type ypb_store_req_t = `YPB_REQ_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_store_rsp_t = `YPB_RSP_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_amo_req_t = `YPB_REQ_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_amo_rsp_t = `YPB_RSP_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_load_req_t = `YPB_REQ_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_load_rsp_t = `YPB_RSP_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_mmu_ptw_req_t = `YPB_REQ_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_mmu_ptw_rsp_t = `YPB_RSP_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_zcmt_req_t = `YPB_REQ_T(CVA6Cfg, CVA6Cfg.XLEN);
  localparam type ypb_zcmt_rsp_t = `YPB_RSP_T(CVA6Cfg, CVA6Cfg.XLEN);


  logic icache_enable;
  logic icache_flush;
  logic icache_miss;

  logic dcache_enable;
  logic dcache_flush;
  logic dcache_flush_ack;
  logic dcache_miss;

  logic wbuffer_empty;
  logic wbuffer_not_ni;


  ypb_fetch_req_t ypb_fetch_req;
  ypb_fetch_rsp_t ypb_fetch_rsp;

  ypb_store_req_t ypb_store_req;
  ypb_store_rsp_t ypb_store_rsp;

  ypb_amo_req_t ypb_amo_req;
  ypb_amo_rsp_t ypb_amo_rsp;

  ypb_load_req_t ypb_load_req;
  ypb_load_rsp_t ypb_load_rsp;

  ypb_mmu_ptw_req_t ypb_mmu_ptw_req;
  ypb_mmu_ptw_rsp_t ypb_mmu_ptw_rsp;

  ypb_zcmt_req_t ypb_zcmt_req;
  ypb_zcmt_rsp_t ypb_zcmt_rsp;

  // -------------------
  // Pipeline
  // -------------------

  cva6_pipeline #(
      // CVA6 config
      .CVA6Cfg            (CVA6Cfg),
      // RVFI PROBES
      .rvfi_probes_t      (rvfi_probes_t),
      // YPB 
      .ypb_fetch_req_t    (ypb_fetch_req_t),
      .ypb_fetch_rsp_t    (ypb_fetch_rsp_t),
      .ypb_store_req_t    (ypb_store_req_t),
      .ypb_store_rsp_t    (ypb_store_rsp_t),
      .ypb_amo_req_t      (ypb_amo_req_t),
      .ypb_amo_rsp_t      (ypb_amo_rsp_t),
      .ypb_load_req_t     (ypb_load_req_t),
      .ypb_load_rsp_t     (ypb_load_rsp_t),
      .ypb_mmu_ptw_req_t  (ypb_mmu_ptw_req_t),
      .ypb_mmu_ptw_rsp_t  (ypb_mmu_ptw_rsp_t),
      .ypb_zcmt_req_t     (ypb_zcmt_req_t),
      .ypb_zcmt_rsp_t     (ypb_zcmt_rsp_t),
      // CVXIF
      .readregflags_t     (readregflags_t),
      .writeregflags_t    (writeregflags_t),
      .id_t               (id_t),
      .hartid_t           (hartid_t),
      .x_compressed_req_t (x_compressed_req_t),
      .x_compressed_resp_t(x_compressed_resp_t),
      .x_issue_req_t      (x_issue_req_t),
      .x_issue_resp_t     (x_issue_resp_t),
      .x_register_t       (x_register_t),
      .x_commit_t         (x_commit_t),
      .x_result_t         (x_result_t),
      .cvxif_req_t        (cvxif_req_t),
      .cvxif_resp_t       (cvxif_resp_t)
      //
  ) i_cva6_pipeline (
      .clk_i(clk_i),
      .rst_ni(rst_ni),
      .boot_addr_i(boot_addr_i),
      .hart_id_i(hart_id_i),
      .irq_i(irq_i),
      .ipi_i(ipi_i),
      .time_irq_i(time_irq_i),
      .debug_req_i(debug_req_i),
      .rvfi_probes_o(rvfi_probes_o),
      .cvxif_req_o(cvxif_req_o),
      .cvxif_resp_i(cvxif_resp_i),

      // FROM/TO ICACHE SUBSYSTEM

      .icache_enable_o(icache_enable),
      .icache_flush_o (icache_flush),
      .icache_miss_i  (icache_miss),

      .ypb_fetch_req_o(ypb_fetch_req),
      .ypb_fetch_rsp_i(ypb_fetch_rsp),

      // FROM/TO DCACHE SUBSYSTEM

      .dcache_enable_o   (dcache_enable),
      .dcache_flush_o    (dcache_flush),
      .dcache_flush_ack_i(dcache_flush_ack),
      .dcache_miss_i     (dcache_miss),

      .ypb_store_req_o  (ypb_store_req),
      .ypb_store_rsp_i  (ypb_store_rsp),
      .ypb_amo_req_o    (ypb_amo_req),
      .ypb_amo_rsp_i    (ypb_amo_rsp),
      .ypb_load_req_o   (ypb_load_req),
      .ypb_load_rsp_i   (ypb_load_rsp),
      .ypb_mmu_ptw_req_o(ypb_mmu_ptw_req),
      .ypb_mmu_ptw_rsp_i(ypb_mmu_ptw_rsp),
      .ypb_zcmt_req_o   (ypb_zcmt_req),
      .ypb_zcmt_rsp_i   (ypb_zcmt_rsp),

      .dcache_wbuffer_empty_i (wbuffer_empty),
      .dcache_wbuffer_not_ni_i(wbuffer_not_ni)
  );


  if (CVA6Cfg.PipelineOnly) begin : gen_obi_adapter

    // -------------------
    // OBI Adapter
    // -------------------

    cva6_obi_adapter_subsystem #(
        .CVA6Cfg          (CVA6Cfg),
        .ypb_fetch_req_t  (ypb_fetch_req_t),
        .ypb_fetch_rsp_t  (ypb_fetch_rsp_t),
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
        .noc_req_t        (noc_req_t),
        .noc_resp_t       (noc_resp_t)

    ) i_cva6_obi_adapter_subsystem (
        .clk_i (clk_i),
        .rst_ni(rst_ni),

        // FROM/TO PIPELINE (YPB)

        .ypb_fetch_req_i  (ypb_fetch_req),
        .ypb_fetch_rsp_o  (ypb_fetch_rsp),
        .ypb_store_req_i  (ypb_store_req),
        .ypb_store_rsp_o  (ypb_store_rsp),
        .ypb_amo_req_i    (ypb_amo_req),
        .ypb_amo_rsp_o    (ypb_amo_rsp),
        .ypb_load_req_i   (ypb_load_req),
        .ypb_load_rsp_o   (ypb_load_rsp),
        .ypb_mmu_ptw_req_i(ypb_mmu_ptw_req),
        .ypb_mmu_ptw_rsp_o(ypb_mmu_ptw_rsp),
        .ypb_zcmt_req_i   (ypb_zcmt_req),
        .ypb_zcmt_rsp_o   (ypb_zcmt_rsp),

        // CACHE CONTROL (NO USED)

        .icache_en_i       (icache_enable),
        .icache_flush_i    (icache_flush),
        .icache_miss_o     (icache_miss),
        .dcache_enable_i   (dcache_enable),
        .dcache_flush_i    (dcache_flush),
        .dcache_flush_ack_o(dcache_flush_ack),
        .dcache_miss_o     (dcache_miss),
        .wbuffer_empty_o   (wbuffer_empty),
        .wbuffer_not_ni_o  (wbuffer_not_ni),

        // FROM/TO NOC (OBI)

        .noc_req_o (noc_req_o),
        .noc_resp_i(noc_resp_i)
    );

  end else begin : gen_cache_subsystem

    // -------------------
    // Cache Subsystem
    // -------------------

    cva6_hpdcache_subsystem #(
        .CVA6Cfg          (CVA6Cfg),
        .ypb_fetch_req_t  (ypb_fetch_req_t),
        .ypb_fetch_rsp_t  (ypb_fetch_rsp_t),
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
        .noc_req_t        (noc_req_t),
        .noc_resp_t       (noc_resp_t),
        .cmo_req_t        (logic  /*FIXME*/),
        .cmo_rsp_t        (logic  /*FIXME*/)
    ) i_cache_subsystem (
        .clk_i (clk_i),
        .rst_ni(rst_ni),

        // FROM/TO FETCH

        .icache_en_i   (icache_enable),
        .icache_flush_i(icache_flush),
        .icache_miss_o (icache_miss),

        // FETCH FROM/TO PIPELINE (YPB)

        .ypb_fetch_req_i(ypb_fetch_req),
        .ypb_fetch_rsp_o(ypb_fetch_rsp),

        // FROM/TO LSU

        .dcache_enable_i   (dcache_enable),
        .dcache_flush_i    (dcache_flush),
        .dcache_flush_ack_o(dcache_flush_ack),
        .dcache_miss_o     (dcache_miss),

        // DATA FROM/TO PIPELINE (YPB)

        .ypb_store_req_i  (ypb_store_req),
        .ypb_store_rsp_o  (ypb_store_rsp),
        .ypb_amo_req_i    (ypb_amo_req),
        .ypb_amo_rsp_o    (ypb_amo_rsp),
        .ypb_load_req_i   (ypb_load_req),
        .ypb_load_rsp_o   (ypb_load_rsp),
        .ypb_mmu_ptw_req_i(ypb_mmu_ptw_req),
        .ypb_mmu_ptw_rsp_o(ypb_mmu_ptw_rsp),
        .ypb_zcmt_req_i   (ypb_zcmt_req),
        .ypb_zcmt_rsp_o   (ypb_zcmt_rsp),

        .wbuffer_empty_o (wbuffer_empty),
        .wbuffer_not_ni_o(wbuffer_not_ni),

        // FROM/TO CMO

        .dcache_cmo_req_i('0  /*FIXME*/),
        .dcache_cmo_rsp_o(  /*FIXME*/),

        // FROM/TO HW PREFETCHER

        .hwpf_base_set_i    ('0  /*FIXME*/),
        .hwpf_base_i        ('0  /*FIXME*/),
        .hwpf_base_o        (  /*FIXME*/),
        .hwpf_param_set_i   ('0  /*FIXME*/),
        .hwpf_param_i       ('0  /*FIXME*/),
        .hwpf_param_o       (  /*FIXME*/),
        .hwpf_throttle_set_i('0  /*FIXME*/),
        .hwpf_throttle_i    ('0  /*FIXME*/),
        .hwpf_throttle_o    (  /*FIXME*/),
        .hwpf_status_o      (  /*FIXME*/),

        // FROM/TO NOC (AXI)

        .noc_req_o (noc_req_o),
        .noc_resp_i(noc_resp_i)
    );

  end

endmodule  // ariane
