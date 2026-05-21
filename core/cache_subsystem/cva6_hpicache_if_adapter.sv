// Copyright 2023 Commissariat a l'Energie Atomique et aux Energies
//                Alternatives (CEA)
// Copyright 2025 Inria, Universite Grenoble Alpes
//
// Licensed under the Solderpad Hardware License, Version 2.1 (the “License”);
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Authors: Cesar Fuguet
// Date: June, 2025
// Description: Interface adapter for the CVA6 core fetch interface
//
// Additional contributions by:
// June, 2025 - Yannick Casamatta, Thales : YBP Protocol

module cva6_hpicache_if_adapter
//  Parameters
//  {{{
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter hpdcache_pkg::hpdcache_cfg_t HPDcacheCfg = '0,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_req_offset_t = logic,
    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic,
    parameter type ypb_fetch_req_t = logic,
    parameter type ypb_fetch_rsp_t = logic
)
//  }}}

//  Ports
//  {{{
(
    //  Clock and active-low reset pins
    input logic clk_i,
    input logic rst_ni,

    //  Request/response ports from/to the CVA6 core
    input  ypb_fetch_req_t ypb_fetch_req_i,
    output ypb_fetch_rsp_t ypb_fetch_rsp_o,

    //  Icache flush signal
    input  logic cva6_icache_flush_i,
    output logic cva6_icache_flush_ack_o,

    //  Request port to the L1 Icache
    output logic                        hpicache_req_valid_o,
    input  logic                        hpicache_req_ready_i,
    output hpdcache_req_t               hpicache_req_o,
    output logic                        hpicache_req_abort_o,
    output hpdcache_tag_t               hpicache_req_tag_o,
    output hpdcache_pkg::hpdcache_pma_t hpicache_req_pma_o,

    //  Response port from the L1 Icache
    input logic          hpicache_rsp_valid_i,
    input hpdcache_rsp_t hpicache_rsp_i
);
  //  }}}

  //  Internal nets and registers
  //  {{{
  typedef enum {
    FLUSH_IDLE,
    FLUSH_PEND
  } flush_fsm_t;

  // ----------------------
  // Addr split Functions
  // ----------------------
  // extract Icache tag from addr
  function automatic logic [CVA6Cfg.ICACHE_TAG_WIDTH-1:0] get_icache_addr_tag(
      logic [CVA6Cfg.PLEN-1:0] addr);
    return addr[CVA6Cfg.ICACHE_TAG_WIDTH+CVA6Cfg.ICACHE_INDEX_WIDTH-1 : CVA6Cfg.ICACHE_INDEX_WIDTH];
  endfunction

  // extract Icache index from addr
  function automatic logic [CVA6Cfg.ICACHE_INDEX_WIDTH-1:0] get_icache_addr_index(
      logic [CVA6Cfg.PLEN-1:0] addr);
    return addr[CVA6Cfg.ICACHE_INDEX_WIDTH-1:0];
  endfunction
  //  }}}

  //  Request forwarding
  //  {{{
  logic hpicache_req_is_uncacheable;
  hpdcache_req_t hpicache_req;
  hpdcache_req_t hpicache_req_fetch;
  hpdcache_req_t hpicache_req_flush;
  logic forward_fetch, forward_flush;
  logic flush_not_sent;

  //  ICACHE flush request
  //  {{{
  flush_fsm_t flush_fsm_q, flush_fsm_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : flush_ff
    if (!rst_ni) begin
      flush_fsm_q <= FLUSH_IDLE;
    end else begin
      flush_fsm_q <= flush_fsm_d;

      if (flush_fsm_q == FLUSH_IDLE && cva6_icache_flush_i && !hpicache_req_ready_i)
        flush_not_sent <= '1;
      else flush_not_sent <= forward_flush;
    end
  end

  always_comb begin : flush_comb
    forward_flush = 1'b0;
    cva6_icache_flush_ack_o = 1'b0;

    flush_fsm_d = flush_fsm_q;

    case (flush_fsm_q)
      FLUSH_IDLE: begin
        if (cva6_icache_flush_i || flush_not_sent) begin
          forward_flush = 1'b1;
          if (hpicache_req_ready_i) begin
            flush_fsm_d = FLUSH_PEND;
          end
        end
      end
      FLUSH_PEND: begin
        if (hpicache_rsp_valid_i) begin
          if (hpicache_rsp_i.tid == '1) begin
            cva6_icache_flush_ack_o = 1'b1;
            flush_fsm_d = FLUSH_IDLE;
          end
        end
      end
      default: begin
      end
    endcase
  end
  //  }}}

  assign forward_fetch = ypb_fetch_req_i.preq;

  assign hpicache_req_fetch = '{
          addr_offset: get_icache_addr_index(ypb_fetch_req_i.paddr),
          wdata: ypb_fetch_req_i.wdata,
          op: hpdcache_pkg::HPDCACHE_REQ_LOAD,
          be: ypb_fetch_req_i.be,
          size: ypb_fetch_req_i.size,
          sid: '0,
          tid: '0,
          need_rsp: 1'b1,
          phys_indexed: 1'b1,
          addr_tag: get_icache_addr_tag(ypb_fetch_req_i.paddr),
          pma: '{
              uncacheable: !ypb_fetch_req_i.cacheable,
              io: 1'b0,
              wr_policy_hint: hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO
          }
      };



  assign hpicache_req_flush = '{
          addr_offset: '0,
          addr_tag: '0,
          wdata: '0,
          op: hpdcache_pkg::HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL,
          be: '0,
          size: '0,
          sid: '0,
          tid: '1,
          need_rsp: 1'b1,
          phys_indexed: 1'b0,
          pma: '{
              uncacheable: 1'b0,
              io: 1'b0,
              wr_policy_hint: hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO
          }
      };

  assign hpicache_req_valid_o = forward_fetch | forward_flush;
  assign hpicache_req = forward_flush ? hpicache_req_flush : hpicache_req_fetch; //flush has higher priority
  assign hpicache_req_abort_o = 1'b0;  // unused on physically indexed requests
  assign hpicache_req_tag_o = '0;  // unused on physically indexed requests
  assign hpicache_req_pma_o.uncacheable = 1'b0;
  assign hpicache_req_pma_o.io = 1'b0;
  assign hpicache_req_pma_o.wr_policy_hint = hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO;
  assign hpicache_req_o = hpicache_req;
  //  }}}

  //  Response forwarding
  //  {{{
  logic ypb_fetch_valid;
  assign ypb_fetch_valid = hpicache_rsp_valid_i && (hpicache_rsp_i.tid != '1);
  assign ypb_fetch_rsp_o.pgnt = hpicache_req_ready_i & ypb_fetch_req_i.preq & !cva6_icache_flush_i;
  assign ypb_fetch_rsp_o.vgnt = ypb_fetch_req_i.vreq;
  assign ypb_fetch_rsp_o.rvalid = ypb_fetch_valid;
  assign ypb_fetch_rsp_o.rid = hpicache_rsp_i.tid;
  assign ypb_fetch_rsp_o.err = '0;
  assign ypb_fetch_rsp_o.rdata = hpicache_rsp_i.rdata;
  //  }}}
  xlnx_ila ila (
      .clk(clk_i),
      .probe0(ypb_fetch_req_i.preq),
      .probe1(ypb_fetch_req_i.paddr),
      .probe2(ypb_fetch_req_i.vreq),
      .probe3(ypb_fetch_req_i.vaddr),
      .probe4(ypb_fetch_req_i.we),
      .probe5(ypb_fetch_req_i.wdata),
      .probe6(ypb_fetch_req_i.aid),
      .probe7(ypb_fetch_req_i.atop),
      .probe8(ypb_fetch_req_i.cacheable),
      .probe9(ypb_fetch_req_i.kill_req),
      .probe10(ypb_fetch_req_i.rready),
      .probe11(ypb_fetch_rsp_o.vgnt),
      .probe12(ypb_fetch_rsp_o.pgnt),
      .probe13(ypb_fetch_rsp_o.rvalid),
      .probe14(ypb_fetch_rsp_o.rdata),
      .probe15(ypb_fetch_rsp_o.rid),
      .probe16(ypb_fetch_rsp_o.err),
      .probe17(cva6_icache_flush_i),
      .probe18(cva6_icache_flush_ack_o),
      .probe19(hpicache_req_valid_o),
      .probe20(hpicache_req_ready_i),
      .probe21(hpicache_req_o.addr_offset),
      .probe22(hpicache_req_o.wdata),
      .probe23(hpicache_req_o.op),
      .probe24(hpicache_req_o.tid),
      .probe25(hpicache_req_o.need_rsp),
      .probe26(hpicache_req_o.pma.uncacheable),
      .probe27(hpicache_req_abort_o),
      .probe28(hpicache_req_tag_o),
      .probe29(hpicache_rsp_valid_i),
      .probe30(hpicache_rsp_i.rdata),
      .probe31(hpicache_rsp_i.tid),
      .probe32(forward_flush),
      .probe33(flush_fsm_q)

  );
  //  Assertions
  //  {{{
`ifndef HPDCACHE_ASSERT_OFF
  forward_one_request_assert :
  assert property (@(posedge clk_i) disable iff (rst_ni !== 1'b1) ($onehot0(
      {forward_fetch, forward_flush}
  )))
  else $error("Only one request shall be forwarded");

  v_and_p_request_active_assert :
  assert property (@(posedge clk_i) disable iff (rst_ni !== 1'b1)
      (ypb_fetch_req_i.preq |-> ypb_fetch_req_i.vreq))
  else $error("Fetch physical requests imply a virtual request");
`endif  // HPDCACHE_ASSERT_OFF
  //  }}}

endmodule
