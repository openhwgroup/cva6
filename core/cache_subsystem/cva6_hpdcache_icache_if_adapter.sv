// Copyright 2023 Commissariat a l'Energie Atomique et aux Energies
//                Alternatives (CEA)
//
// Licensed under the Solderpad Hardware License, Version 2.1 (the “License”);
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Authors: Akiho Kawada
// Date: July, 2024
// Description: Icache Interface adapter for the CVA6 core
module cva6_hpdcache_icache_if_adapter
//  Parameters
//  {{{
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter hpdcache_pkg::hpdcache_cfg_t hpdcacheCfg = '0,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_req_offset_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic,
    parameter type fetch_dreq_t = logic,
    parameter type fetch_drsp_t = logic,
    parameter type obi_fetch_req_t = logic,
    parameter type obi_fetch_rsp_t = logic,
    parameter logic [CVA6Cfg.MEM_TID_WIDTH-1:0] RdTxId = 0  // TODO
)
//  }}}

//  Ports
//  {{{
(
    //  Clock and active-low reset pins
    input logic clk_i,
    input logic rst_ni,

    //  Port ID
    input hpdcache_req_sid_t hpdcache_req_sid_i,

    //  Request/response ports from/to the CVA6 core
    input fetch_dreq_t dreq_i,
    output fetch_drsp_t dreq_o,
    input obi_fetch_req_t fetch_obi_req_i,
    output obi_fetch_rsp_t fetch_obi_rsp_o,

    //  Request port to the L1 Dcache
    output logic                        hpdcache_req_valid_o,
    input  logic                        hpdcache_req_ready_i,
    output hpdcache_req_t               hpdcache_req_o,
    output logic                        hpdcache_req_abort_o,
    output hpdcache_tag_t               hpdcache_req_tag_o,
    output hpdcache_pkg::hpdcache_pma_t hpdcache_req_pma_o,

    //  Response port from the L1 Dcache
    input logic          hpdcache_rsp_valid_i,
    input hpdcache_rsp_t hpdcache_rsp_i
);
  //  }}}

  // localparam ICACHE_OFFSET_WIDTH = $clog2(CVA6Cfg.ICACHE_LINE_WIDTH / 8);
  localparam ICACHE_OFFSET_WIDTH = 3;
  localparam int ICACHE_CL_SIZE = $clog2(CVA6Cfg.ICACHE_LINE_WIDTH / 8);
  localparam int ICACHE_WORD_SIZE = 3;
  localparam int ICACHE_MEM_REQ_CL_SIZE =
    (CVA6Cfg.AxiDataWidth <= CVA6Cfg.ICACHE_LINE_WIDTH) ?
      $clog2(
      CVA6Cfg.AxiDataWidth / 8
  ) : ICACHE_CL_SIZE;

  //  Internal nets and registers
  //  {{{
  logic hpdcache_req_is_uncacheable;
  logic va_transferred_q, va_transferred_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : transferred_state_magnegement
    if (!rst_ni) begin
      va_transferred_q <= '0;
    end else begin
      va_transferred_q <= va_transferred_d;
    end
  end

  assign va_transferred_d = dreq_i.req & hpdcache_req_ready_i;
  //  }}}

  //  Request forwarding
  //  {{{
  assign hpdcache_req_is_uncacheable = !config_pkg::is_inside_cacheable_regions(
      CVA6Cfg,
      {
        {64 - CVA6Cfg.PLEN{1'b0}},
        fetch_obi_req_i.a.addr[CVA6Cfg.ICACHE_TAG_WIDTH+CVA6Cfg.ICACHE_INDEX_WIDTH-1:CVA6Cfg.ICACHE_INDEX_WIDTH], // TODO
        {CVA6Cfg.ICACHE_INDEX_WIDTH{1'b0}}
      }
  );

  //    Request forwarding
  assign hpdcache_req_valid_o = dreq_i.req,
      hpdcache_req_o.addr_offset = dreq_i.vaddr[CVA6Cfg.ICACHE_INDEX_WIDTH-1:0],
      hpdcache_req_o.wdata = '0,
      hpdcache_req_o.op = hpdcache_pkg::HPDCACHE_REQ_LOAD,
      hpdcache_req_o.be = fetch_obi_req_i.a.be,
      hpdcache_req_o.size = hpdcache_req_is_uncacheable ? ICACHE_WORD_SIZE : ICACHE_MEM_REQ_CL_SIZE, // TODO
      hpdcache_req_o.sid = '0,
      hpdcache_req_o.tid = RdTxId,  // TODO 
      hpdcache_req_o.need_rsp = 1'b1,
      hpdcache_req_o.phys_indexed = 1'b0,
      hpdcache_req_o.addr_tag = '0,  // unused on virtually indexed request
      hpdcache_req_o.pma = '0;  // unused on virtually indexed request

  assign hpdcache_req_abort_o = va_transferred_q & (dreq_i.kill_req | ~fetch_obi_req_i.req),
      hpdcache_req_tag_o = fetch_obi_req_i.a.addr[CVA6Cfg.ICACHE_TAG_WIDTH+CVA6Cfg.ICACHE_INDEX_WIDTH-1:CVA6Cfg.ICACHE_INDEX_WIDTH],
      hpdcache_req_pma_o.uncacheable = hpdcache_req_is_uncacheable,
      hpdcache_req_pma_o.io = 1'b0;

  //    Response forwarding
  assign dreq_o.ready = hpdcache_req_ready_i;
  //   dreq_o.invalid_data = hpdcache_req_ready_i; // need this? (valid or killed)
  logic obi_gnt_q, obi_gnt_d;  // TODO, need to fix

  assign obi_gnt_d = fetch_obi_req_i.req;

  always_ff @(posedge clk_i or negedge rst_ni) begin : obi_gnt_gen  // TODO
    if (!rst_ni) begin
      obi_gnt_q <= '0;
    end else begin
      obi_gnt_q <= obi_gnt_d;
    end
  end

  logic which_half_d, which_half_q;
  assign which_half_d = (fetch_obi_req_i.req) ? fetch_obi_req_i.a.addr[2] : which_half_q;


  always_ff @(posedge clk_i or negedge rst_ni) begin : gen_offset
    if (!rst_ni) begin
      which_half_q <= '0;
    end else begin
      which_half_q <= which_half_d;
    end
  end

  assign fetch_obi_rsp_o.gnt = obi_gnt_q,
      fetch_obi_rsp_o.gntpar = !obi_gnt_q,
      fetch_obi_rsp_o.rvalid = hpdcache_rsp_valid_i,
      fetch_obi_rsp_o.rvalidpar = !hpdcache_rsp_valid_i,
      fetch_obi_rsp_o.r.rid = hpdcache_rsp_i.tid,
      fetch_obi_rsp_o.r.r_optional.exokay = '0,
      fetch_obi_rsp_o.r.r_optional.rchk = '0,
      fetch_obi_rsp_o.r.err = hpdcache_rsp_i.error,
      fetch_obi_rsp_o.r.rdata = hpdcache_rsp_i.rdata[0][{
        which_half_q, 5'b0
      }+:CVA6Cfg.FETCH_WIDTH],
      fetch_obi_rsp_o.r.r_optional.ruser = '0;  // TODO
  //  }}}
  //  }}}

endmodule
