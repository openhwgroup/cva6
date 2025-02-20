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

`include "obi/typedef.svh"
`include "obi/assign.svh"
`include "rvfi_types.svh"
`include "cvxif_types.svh"

module cva6
  import ariane_pkg::*;
#(
    // CVA6 config
    parameter config_pkg::cva6_cfg_t CVA6Cfg = build_config_pkg::build_config(
        cva6_config_pkg::cva6_cfg
    ),

    // RVFI PROBES
    localparam type rvfi_probes_instr_t = `RVFI_PROBES_INSTR_T(CVA6Cfg),
    localparam type rvfi_probes_csr_t = `RVFI_PROBES_CSR_T(CVA6Cfg),
    parameter type rvfi_probes_t = struct packed {
      rvfi_probes_csr_t   csr;
      rvfi_probes_instr_t instr;
    },

    localparam type icache_req_t = struct packed {
      logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] way;  // way to replace
      logic [CVA6Cfg.PLEN-1:0] paddr;  // physical address
      logic nc;  // noncacheable
      logic [CVA6Cfg.MEM_TID_WIDTH-1:0] tid;  // threadi id (used as transaction id in Ariane)
    },
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
    },

    // AXI types
    localparam type axi_ar_chan_t = struct packed {
      logic [CVA6Cfg.AxiIdWidth-1:0]   id;
      logic [CVA6Cfg.AxiAddrWidth-1:0] addr;
      axi_pkg::len_t                   len;
      axi_pkg::size_t                  size;
      axi_pkg::burst_t                 burst;
      logic                            lock;
      axi_pkg::cache_t                 cache;
      axi_pkg::prot_t                  prot;
      axi_pkg::qos_t                   qos;
      axi_pkg::region_t                region;
      logic [CVA6Cfg.AxiUserWidth-1:0] user;
    },
    localparam type axi_aw_chan_t = struct packed {
      logic [CVA6Cfg.AxiIdWidth-1:0]   id;
      logic [CVA6Cfg.AxiAddrWidth-1:0] addr;
      axi_pkg::len_t                   len;
      axi_pkg::size_t                  size;
      axi_pkg::burst_t                 burst;
      logic                            lock;
      axi_pkg::cache_t                 cache;
      axi_pkg::prot_t                  prot;
      axi_pkg::qos_t                   qos;
      axi_pkg::region_t                region;
      axi_pkg::atop_t                  atop;
      logic [CVA6Cfg.AxiUserWidth-1:0] user;
    },
    localparam type axi_w_chan_t = struct packed {
      logic [CVA6Cfg.AxiDataWidth-1:0]     data;
      logic [(CVA6Cfg.AxiDataWidth/8)-1:0] strb;
      logic                                last;
      logic [CVA6Cfg.AxiUserWidth-1:0]     user;
    },
    localparam type b_chan_t = struct packed {
      logic [CVA6Cfg.AxiIdWidth-1:0]   id;
      axi_pkg::resp_t                  resp;
      logic [CVA6Cfg.AxiUserWidth-1:0] user;
    },
    localparam type r_chan_t = struct packed {
      logic [CVA6Cfg.AxiIdWidth-1:0]   id;
      logic [CVA6Cfg.AxiDataWidth-1:0] data;
      axi_pkg::resp_t                  resp;
      logic                            last;
      logic [CVA6Cfg.AxiUserWidth-1:0] user;
    },
    localparam type noc_req_t = struct packed {
      axi_aw_chan_t aw;
      logic         aw_valid;
      axi_w_chan_t  w;
      logic         w_valid;
      logic         b_ready;
      axi_ar_chan_t ar;
      logic         ar_valid;
      logic         r_ready;
    },
    parameter type noc_resp_t = struct packed {
      logic    aw_ready;
      logic    ar_ready;
      logic    w_ready;
      logic    b_valid;
      b_chan_t b;
      logic    r_valid;
      r_chan_t r;
    },

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

  // Fetch data requests
  localparam type fetch_req_t = struct packed {
    logic                    req;       // we request a new word
    logic                    kill_req;  // kill the last request
    logic [CVA6Cfg.VLEN-1:0] vaddr;     // 1st cycle: 12 bit index is taken for lookup
  };
  localparam type fetch_rsp_t = struct packed {
    logic ready;  // fetch is ready
    logic invalid_data;  // obi data is invalid caused by aborted request kill_req, use for debug
  };

  // OLD data requests TO BE REMOVED
  localparam type dbus_req_t = struct packed {
    logic [CVA6Cfg.DCACHE_INDEX_WIDTH-1:0] address_index;
    logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0]   address_tag;
    logic [CVA6Cfg.XLEN-1:0]               data_wdata;
    logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0]  data_wuser;
    logic                                  data_req;
    logic                                  data_we;
    logic [(CVA6Cfg.XLEN/8)-1:0]           data_be;
    logic [1:0]                            data_size;
    logic [CVA6Cfg.DcacheIdWidth-1:0]      data_id;
    logic                                  kill_req;
    logic                                  tag_valid;
  };
  localparam type dbus_rsp_t = struct packed {
    logic                                 data_gnt;
    logic                                 data_rvalid;
    logic [CVA6Cfg.DcacheIdWidth-1:0]     data_rid;
    logic [CVA6Cfg.XLEN-1:0]              data_rdata;
    logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0] data_ruser;
  };

  // Load requests
  localparam type load_req_t = struct packed {
    logic [CVA6Cfg.DCACHE_INDEX_WIDTH-1:0] address_index;
    logic                                  req;
    logic [(CVA6Cfg.XLEN/8)-1:0]           be;
    logic [CVA6Cfg.IdWidth-1:0]            aid;
    logic                                  kill_req;
  };

  localparam type load_rsp_t = struct packed {logic gnt;};

  //OBI FETCH
  `OBI_LOCALPARAM_TYPE_ALL(obi_fetch, CVA6Cfg.ObiFetchbusCfg);
  //OBI STORE
  `OBI_LOCALPARAM_TYPE_ALL(obi_store, CVA6Cfg.ObiStorebusCfg);
  //OBI AMO
  `OBI_LOCALPARAM_TYPE_ALL(obi_amo, CVA6Cfg.ObiAmobusCfg);
  //OBI LOAD
  `OBI_LOCALPARAM_TYPE_ALL(obi_load, CVA6Cfg.ObiLoadbusCfg);
  //OBI MMU_PTW
  //`OBI_LOCALPARAM_TYPE_ALL(obi_mmu_ptw, CVA6Cfg.ObiMmuPtwbusCfg);
  //OBI ZCMT
  //`OBI_LOCALPARAM_TYPE_ALL(obi_zcmt, CVA6Cfg.ObiZcmtbusCfg)

  //FIXME temp
  localparam type obi_mmu_ptw_req_t = dbus_req_t;
  localparam type obi_mmu_ptw_rsp_t = dbus_rsp_t;
  localparam type obi_zcmt_req_t = dbus_req_t;
  localparam type obi_zcmt_rsp_t = dbus_rsp_t;

  logic icache_en;
  logic icache_flush;
  logic icache_miss;

  logic dcache_enable;
  logic dcache_flush;
  logic dcache_flush_ack;
  logic dcache_miss;

  logic wbuffer_empty;
  logic wbuffer_not_ni;

  fetch_req_t fetch_req;
  fetch_rsp_t fetch_rsp;
  obi_fetch_req_t obi_fetch_req;
  obi_fetch_rsp_t obi_fetch_rsp;

  obi_store_req_t obi_store_req;
  obi_store_rsp_t obi_store_rsp;

  obi_amo_req_t obi_amo_req;
  obi_amo_rsp_t obi_amo_rsp;

  load_req_t load_req;
  load_rsp_t load_rsp;
  obi_load_req_t obi_load_req;
  obi_load_rsp_t obi_load_rsp;

  obi_mmu_ptw_req_t obi_mmu_ptw_req;
  obi_mmu_ptw_rsp_t obi_mmu_ptw_rsp;

  obi_zcmt_req_t obi_zcmt_req;
  obi_zcmt_rsp_t obi_zcmt_rsp;

  // -------------------
  // Pipeline
  // -------------------

  cva6_pipeline #(
      // CVA6 config
      .CVA6Cfg(CVA6Cfg),
      // RVFI PROBES
      .rvfi_probes_t(rvfi_probes_t)
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

      .fetch_req_o (fetch_req),
      .fetch_rsp_i (fetch_rsp),
      .obi_fetch_req_o   (obi_fetch_req),
      .obi_fetch_rsp_i   (obi_fetch_rsp),

      // FROM/TO DCACHE SUBSYSTEM

      .dcache_enable_o   (dcache_enable),
      .dcache_flush_o    (dcache_flush),
      .dcache_flush_ack_i(dcache_flush_ack),
      .dcache_miss_i     (dcache_miss),

      .obi_store_req_o  (obi_store_req),
      .obi_store_rsp_i  (obi_store_rsp),
      .obi_amo_req_o    (obi_amo_req),
      .obi_amo_rsp_i    (obi_amo_rsp),
      .load_req_o       (load_req),
      .load_rsp_i       (load_rsp),
      .obi_load_req_o   (obi_load_req),
      .obi_load_rsp_i   (obi_load_rsp),
      .obi_mmu_ptw_req_o(obi_mmu_ptw_req),
      .obi_mmu_ptw_rsp_i(obi_mmu_ptw_rsp),
      .obi_zcmt_req_o   (obi_zcmt_req),
      .obi_zcmt_rsp_i   (obi_zcmt_rsp),

      .dcache_wbuffer_empty_i (wbuffer_empty),
      .dcache_wbuffer_not_ni_i(wbuffer_not_ni)
  );

  // -------------------
  // Cache Subsystem
  // -------------------

  cva6_hpdcache_subsystem #(
      .CVA6Cfg          (CVA6Cfg),
      .fetch_req_t      (fetch_req_t),
      .fetch_rsp_t      (fetch_rsp_t),
      .obi_fetch_req_t  (obi_fetch_req_t),
      .obi_fetch_rsp_t  (obi_fetch_rsp_t),
      .icache_req_t     (icache_req_t),
      .icache_rtrn_t    (icache_rtrn_t),
      .load_req_t       (load_req_t),
      .load_rsp_t       (load_rsp_t),
      .obi_store_req_t  (obi_store_req_t),
      .obi_store_rsp_t  (obi_store_rsp_t),
      .obi_amo_req_t    (obi_amo_req_t),
      .obi_amo_rsp_t    (obi_amo_rsp_t),
      .obi_load_req_t   (obi_load_req_t),
      .obi_load_rsp_t   (obi_load_rsp_t),
      .obi_mmu_ptw_req_t(obi_mmu_ptw_req_t),
      .obi_mmu_ptw_rsp_t(obi_mmu_ptw_rsp_t),
      .obi_zcmt_req_t   (obi_zcmt_req_t),
      .obi_zcmt_rsp_t   (obi_zcmt_rsp_t),
      .axi_ar_chan_t    (axi_ar_chan_t),
      .axi_aw_chan_t    (axi_aw_chan_t),
      .axi_w_chan_t     (axi_w_chan_t),
      .axi_b_chan_t     (b_chan_t),
      .axi_r_chan_t     (r_chan_t),
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

      .fetch_req_i (fetch_req),
      .fetch_rsp_o (fetch_rsp),
      .obi_fetch_req_i   (obi_fetch_req),
      .obi_fetch_rsp_o   (obi_fetch_rsp),

      // FROM/TO LSU

      .dcache_enable_i   (dcache_enable),
      .dcache_flush_i    (dcache_flush),
      .dcache_flush_ack_o(dcache_flush_ack),
      .dcache_miss_o     (dcache_miss),

      .obi_store_req_i  (obi_store_req),
      .obi_store_rsp_o  (obi_store_rsp),
      .obi_amo_req_i    (obi_amo_req),
      .obi_amo_rsp_o    (obi_amo_rsp),
      .load_req_i       (load_req),
      .load_rsp_o       (load_rsp),
      .obi_load_req_i   (obi_load_req),
      .obi_load_rsp_o   (obi_load_rsp),
      .obi_mmu_ptw_req_i(obi_mmu_ptw_req),
      .obi_mmu_ptw_rsp_o(obi_mmu_ptw_rsp),
      .obi_zcmt_req_i   (obi_zcmt_req),
      .obi_zcmt_rsp_o   (obi_zcmt_rsp),

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

      // FROM/TO NOC

      .noc_req_o (noc_req_o),
      .noc_resp_i(noc_resp_i)
  );

endmodule  // ariane
