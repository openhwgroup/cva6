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

module extended_hpdcache_subsystem
//  Parameters
//  {{{
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type icache_areq_t = logic,
    parameter type icache_arsp_t = logic,
    parameter type icache_dreq_t = logic,
    parameter type icache_drsp_t = logic,
    parameter type icache_req_t = logic,
    parameter type icache_rtrn_t = logic,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter int NumPorts = 4,
    parameter int NrHwPrefetchers = 4,
    // AXI types
    parameter type axi_ar_chan_t = logic,
    parameter type axi_aw_chan_t = logic,
    parameter type axi_w_chan_t = logic,
    parameter type axi_b_chan_t = logic,
    parameter type axi_r_chan_t = logic,
    parameter type noc_req_t = logic,
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
    //    Cache management
    // Data cache enable - CSR_REGFILE
    input  logic icache_enable_i,
    // Data cache flush - CONTROLLER
    input  logic icache_flush_i,
    // Flush acknowledge - CONTROLLER
    output logic icache_flush_ack_o,
    // Load or store miss - PERF_COUNTERS
    output logic icache_miss_o,

    // AMO request - EX_STAGE
    input  ariane_pkg::amo_req_t                 icache_amo_req_i,
    // AMO response - EX_STAGE
    output ariane_pkg::amo_resp_t                icache_amo_resp_o,
    // CMO interface request - TO_BE_COMPLETED
    input  cmo_req_t                             icache_cmo_req_i,
    // CMO interface response - TO_BE_COMPLETED
    output cmo_rsp_t                             icache_cmo_resp_o,
    // Data cache input request ports - EX_STAGE
    input  icache_req_i_t         [NumPorts-1:0] icache_req_ports_i,
    // Data cache output request ports - EX_STAGE
    output icache_req_o_t         [NumPorts-1:0] icache_req_ports_o,

    //  Hardware memory prefetcher configuration
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0]       icache_hwpf_base_set_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0][63:0] icache_hwpf_base_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic [NrHwPrefetchers-1:0][63:0] icache_hwpf_base_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0]       icache_hwpf_param_set_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0][63:0] icache_hwpf_param_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic [NrHwPrefetchers-1:0][63:0] icache_hwpf_param_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0]       icache_hwpf_throttle_set_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input  logic [NrHwPrefetchers-1:0][63:0] icache_hwpf_throttle_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic [NrHwPrefetchers-1:0][63:0] icache_hwpf_throttle_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic [               63:0]       icache_hwpf_status_o,
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

    // AMO request - EX_STAGE
    input  ariane_pkg::amo_req_t                 dcache_amo_req_i,
    // AMO response - EX_STAGE
    output ariane_pkg::amo_resp_t                dcache_amo_resp_o,
    // CMO interface request - TO_BE_COMPLETED
    input  cmo_req_t                             dcache_cmo_req_i,
    // CMO interface response - TO_BE_COMPLETED
    output cmo_rsp_t                             dcache_cmo_resp_o,
    // Data cache input request ports - EX_STAGE
    input  dcache_req_i_t         [NumPorts-1:0] dcache_req_ports_i,
    // Data cache output request ports - EX_STAGE
    output dcache_req_o_t         [NumPorts-1:0] dcache_req_ports_o,
    // Write buffer status to know if empty - EX_STAGE
    output logic                                 wbuffer_empty_o,
    // Write buffer status to know if not non idempotent - EX_STAGE
    output logic                                 wbuffer_not_ni_o,

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

  //  I$ instantiation
  //  {{{

  logic                 icache_miss_ready;
  logic                 icache_miss_valid;
  hpdcache_mem_req_t    icache_miss;

  logic                 icache_miss_resp_ready;
  logic                 icache_miss_resp_valid;
  hpdcache_mem_resp_r_t icache_miss_resp;

  logic                 icache_uc_read_ready;
  logic                 icache_uc_read_valid;
  hpdcache_mem_req_t    icache_uc_read;

  logic                 icache_uc_read_ready;
  logic                 icache_uc_read_valid;
  hpdcache_mem_req_t    icache_uc_read;

  logic                 icache_uc_read_resp_ready;
  logic                 icache_uc_read_resp_valid;
  hpdcache_mem_resp_r_t icache_uc_read_resp;


  //  {{{
  hpdcache_icache_with_adapter #() i_hpdcache_dcache (
      .icache_enable_i(icache_enable_i),  //
      .icache_flush_i(icache_flush_i),  //
      .icache_flush_ack_o(icache_flush_ack_o),  //
      .icache_miss_o(icache_miss_o),  //
      .icache_amo_req_i(icache_amo_req_i),  //
      .icache_amo_resp_o(icache_amo_resp_o),  //
      .icache_cmo_req_i(icache_cmo_req_i),  //
      .icache_cmo_resp_o(icache_cmo_resp_o),  //
      .icache_req_ports_i(icache_req_ports_i),  //
      .icache_req_ports_o(icache_req_ports_o),  //
      .wbuffer_empty_o(  /**/),  //
      .wbuffer_not_ni_o(  /**/),  //
      .hwpf_base_set_i(icache_hwpf_base_set_i),  //
      .hwpf_base_i(icache_hwpf_base_i),  //
      .hwpf_base_o(icache_hwpf_base_o),  //
      .hwpf_param_set_i(icache_hwpf_param_set_i),  //
      .hwpf_param_i(icache_hwpf_param_i),  //
      .hwpf_param_o(icache_hwpf_param_o),  //
      .hwpf_throttle_set_i(icache_hwpf_throttle_set_i),  //
      .hwpf_throttle_i(icache_hwpf_throttle_i),  //
      .hwpf_throttle_o(icache_hwpf_throttle_o),  //
      .hwpf_status_o(icache_hwpf_status_o),  //

      .icache_miss_ready_i(icache_miss_ready),
      .icache_miss_valid_o(icache_miss_valid),
      .icache_miss_lo(icache_miss),

      .icache_uc_read_ready_i(icache_uc_read_ready),
      .icache_uc_read_valid_o(icache_uc_read_valid),
      .icache_uc_read_o(icache_uc_read),

      .icache_uc_read_resp_ready_o(icache_uc_read_resp_ready),
      .icache_uc_read_resp_valid_i(icache_uc_read_resp_valid),
      .icache_uc_read_resp_i(icache_uc_read_resp),

      .icache_miss_resp_ready_o(icache_miss_resp_ready),
      .icache_miss_resp_valid_i(icache_miss_resp_valid),
      .icache_miss_resp_i(icache_miss_resp)
  );

  //   //  D$ instantiation

  logic                 dcache_miss_ready;
  logic                 dcache_miss_valid;
  hpdcache_mem_req_t    dcache_miss;

  logic                 dcache_miss_resp_ready;
  logic                 dcache_miss_resp_valid;
  hpdcache_mem_resp_r_t dcache_miss_resp;

  logic                 dcache_wbuf_ready;
  logic                 dcache_wbuf_valid;
  hpdcache_mem_req_t    dcache_wbuf;

  logic                 dcache_wbuf_data_ready;
  logic                 dcache_wbuf_data_valid;
  hpdcache_mem_req_w_t  dcache_wbuf_data;

  logic                 dcache_wbuf_resp_ready;
  logic                 dcache_wbuf_resp_valid;
  hpdcache_mem_resp_w_t dcache_wbuf_resp;

  logic                 dcache_uc_read_ready;
  logic                 dcache_uc_read_valid;
  hpdcache_mem_req_t    dcache_uc_read;

  logic                 dcache_uc_read_resp_ready;
  logic                 dcache_uc_read_resp_valid;
  hpdcache_mem_resp_r_t dcache_uc_read_resp;

  logic                 dcache_uc_write_ready;
  logic                 dcache_uc_write_valid;
  hpdcache_mem_req_t    dcache_uc_write;

  logic                 dcache_uc_write_data_ready;
  logic                 dcache_uc_write_data_valid;
  hpdcache_mem_req_w_t  dcache_uc_write_data;

  logic                 dcache_uc_write_resp_ready;
  logic                 dcache_uc_write_resp_valid;
  hpdcache_mem_resp_w_t dcache_uc_write_resp;


  //  {{{
  hpdcache_dcache_with_adapter #() i_hpdcache_dcache (
      .dcache_enable_i(dcache_enable_i),
      .dcache_flush_i(dcache_flush_i),
      .dcache_flush_ack_o(dcache_flush_ack_o),
      .dcache_miss_o(dcache_miss_o),
      .dcache_amo_req_i(dcache_amo_req_i),
      .dcache_amo_resp_o(dcache_amo_resp_o),
      .dcache_cmo_req_i(dcache_cmo_req_i),
      .dcache_cmo_resp_o(dcache_cmo_resp_o),
      .dcache_req_ports_i(dcache_req_ports_i),
      .dcache_req_ports_o(dcache_req_ports_o),
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

      .dcache_miss_ready_i(dcache_miss_ready),
      .dcache_miss_valid_o(dcache_miss_valid),
      .dcache_miss_lo(dcache_miss),

      .dcache_wbuf_data_ready_i(dcache_wbuf_data_ready),
      .dcache_wbuf_data_valid_o(dcache_wbuf_data_valid),
      .dcache_wbuf_data_o(dcache_wbuf_data),

      .dcache_wbuf_resp_ready_o(dcache_wbuf_resp_ready),
      .dcache_wbuf_resp_valid_i(dcache_wbuf_resp_valid),
      .dcache_wbuf_resp_i(dcache_wbuf_resp),

      .dcache_uc_read_ready_i(dcache_uc_read_ready),
      .dcache_uc_read_valid_o(dcache_uc_read_valid),
      .dcache_uc_read_o(dcache_uc_read),

      .dcache_uc_read_resp_ready_o(dcache_uc_read_resp_ready),
      .dcache_uc_read_resp_valid_i(dcache_uc_read_resp_valid),
      .dcache_uc_read_resp_i(dcache_uc_read_resp),

      .dcache_uc_write_ready_i(dcache_uc_write_ready),
      .dcache_uc_write_valid_o(dcache_uc_write_valid),
      .dcache_uc_write_o(dcache_uc_write),

      .dcache_uc_write_data_ready_i(dcache_uc_write_data_ready),
      .dcache_uc_write_data_valid_o(dcache_uc_write_data_valid),
      .dcache_uc_write_data_o(dcache_uc_write_data),

      .dcache_uc_write_resp_ready_o(dcache_uc_write_resp_ready),
      .dcache_uc_write_resp_valid_i(dcache_uc_write_resp_valid),
      .dcache_uc_write_resp_i(dcache_uc_write_resp),

      .dcache_miss_resp_ready_o(dcache_miss_resp_ready),
      .dcache_miss_resp_valid_i(dcache_miss_resp_valid),
      .dcache_miss_resp_i(dcache_miss_resp),

      .dcache_wbuf_o(dcache_wbuf),
      .dcache_wbuf_valid_o(dcache_wbuf_valid),
      .dcache_wbuf_ready_i(dcache_wbuf_ready)
  );
  //  }}}


  //  AXI arbiter instantiation
  //  {{{
  extended_hpdcache_subsystem_axi_arbiter #(
      .CVA6Cfg              (CVA6Cfg),
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

      .icache_miss_ready_o(icache_miss_ready),
      .icache_miss_valid_i(icache_miss_valid),
      .icache_miss_i      (icache_miss),
      .icache_miss_id_i   ('1),                 // TODO

      .icache_miss_resp_ready_i(icache_miss_resp_ready),
      .icache_miss_resp_valid_o(icache_miss_resp_valid),
      .icache_miss_resp_o      (icache_miss_resp),

      .icache_uc_read_ready_o(icache_uc_read_ready),
      .icache_uc_read_valid_i(icache_uc_read_valid),
      .icache_uc_read_i      (icache_uc_read),
      .icache_uc_read_id_i   ('1),                    // TODO

      .icache_uc_read_resp_ready_i(icache_uc_read_resp_ready),
      .icache_uc_read_resp_valid_o(icache_uc_read_resp_valid),
      .icache_uc_read_resp_o      (icache_uc_read_resp),

      .dcache_miss_ready_o(dcache_miss_ready),
      .dcache_miss_valid_i(dcache_miss_valid),
      .dcache_miss_i      (dcache_miss),
      .dcache_miss_id_i   ('1),                 // TODO

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

      .dcache_uc_read_ready_o     (dcache_uc_read_ready),
      .dcache_uc_read_valid_i     (dcache_uc_read_valid),
      .dcache_uc_read_i           (dcache_uc_read),
      .dcache_uc_read_id_i        ('1),                         // TODO
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
