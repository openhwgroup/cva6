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
// Description: Interface adapter for the CVA6 core
module cva6_hpdcache_if_adapter
//  Parameters
//  {{{
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter hpdcache_pkg::hpdcache_cfg_t HPDcacheCfg = '0,
    parameter type hpdcache_tag_t = logic,
    parameter type hpdcache_req_offset_t = logic,
    parameter type hpdcache_req_sid_t = logic,
    parameter type hpdcache_req_t = logic,
    parameter type hpdcache_rsp_t = logic,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter bit InvalidateOnFlush = 1'b0,
    parameter bit IsLoadPort = 1'b1
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
    input  dcache_req_i_t         cva6_req_i,
    output dcache_req_o_t         cva6_req_o,
    input  ariane_pkg::amo_req_t  cva6_amo_req_i,
    output ariane_pkg::amo_resp_t cva6_amo_resp_o,

    //  Dcache flush signal
    input  logic cva6_dcache_flush_i,
    output logic cva6_dcache_flush_ack_o,

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

  //  Internal nets and registers
  //  {{{
  typedef enum {
    FLUSH_IDLE,
    FLUSH_PEND
  } flush_fsm_t;

  logic hpdcache_req_is_uncacheable;
  hpdcache_req_t hpdcache_req;
  //  }}}

  //  Request forwarding
  //  {{{
  generate
    //  LOAD request
    //  {{{
    if (IsLoadPort == 1'b1) begin : load_port_gen
      assign hpdcache_req_is_uncacheable = !config_pkg::is_inside_cacheable_regions(
          CVA6Cfg,
          {
            {64 - CVA6Cfg.DCACHE_TAG_WIDTH{1'b0}}
            , cva6_req_i.address_tag
            , {CVA6Cfg.DCACHE_INDEX_WIDTH{1'b0}}
          }
      );

      //    Request forwarding
      assign hpdcache_req_valid_o = cva6_req_i.data_req;
      assign hpdcache_req.addr_offset = cva6_req_i.address_index;
      assign hpdcache_req.wuser = '0;
      assign hpdcache_req.wdata = '0;
      assign hpdcache_req.op = hpdcache_pkg::HPDCACHE_REQ_LOAD;
      assign hpdcache_req.be = cva6_req_i.data_be;
      assign hpdcache_req.size = cva6_req_i.data_size;
      assign hpdcache_req.sid = hpdcache_req_sid_i;
      assign hpdcache_req.tid = cva6_req_i.data_id;
      assign hpdcache_req.need_rsp = 1'b1;
      assign hpdcache_req.phys_indexed = 1'b0;
      assign hpdcache_req.addr_tag = '0;  // unused on virtually indexed request
      assign hpdcache_req.pma.uncacheable = 1'b0;
      assign hpdcache_req.pma.io = 1'b0;
      assign hpdcache_req.pma.wr_policy_hint = hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO;

      assign hpdcache_req_abort_o = cva6_req_i.kill_req;
      assign hpdcache_req_tag_o = cva6_req_i.address_tag;
      assign hpdcache_req_pma_o.uncacheable = hpdcache_req_is_uncacheable;
      assign hpdcache_req_pma_o.io = 1'b0;
      assign hpdcache_req_pma_o.wr_policy_hint = hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO;

      //    Response forwarding
      assign cva6_req_o.data_rvalid = hpdcache_rsp_valid_i;
      assign cva6_req_o.data_ruser = hpdcache_rsp_i.ruser;
      assign cva6_req_o.data_rdata = hpdcache_rsp_i.rdata;
      assign cva6_req_o.data_rid = hpdcache_rsp_i.tid;
      assign cva6_req_o.data_gnt = hpdcache_req_ready_i;

      //  Assertions
      //  {{{
      //    pragma translate_off
      flush_on_load_port_assert :
      assert property (@(posedge clk_i) disable iff (rst_ni !== 1'b1) (cva6_dcache_flush_i == 1'b0))
      else $error("Flush unsupported on load adapters");
      //    pragma translate_on
      //  }}}
    end  //  }}}

         //  {{{
    else begin : store_amo_gen
      //  STORE/AMO request
      logic                           [ 63:0] amo_addr;
      hpdcache_req_offset_t                   amo_addr_offset;
      hpdcache_tag_t                          amo_tag;
      logic                           [127:0] amo_data;
      logic                                   amo_user;
      logic                           [ 15:0] amo_data_be;
      hpdcache_pkg::hpdcache_req_op_t         amo_op;
      logic                           [127:0] amo_resp;
      logic                                   amo_resp_cap_vld;
      logic                                   amo_pending_q;

      hpdcache_req_t                          hpdcache_req_amo;
      hpdcache_req_t                          hpdcache_req_store;
      hpdcache_req_t                          hpdcache_req_flush;

      flush_fsm_t flush_fsm_q, flush_fsm_d;

      logic forward_store, forward_amo, forward_flush;
      hpdcache_pkg::hpdcache_req_op_t store_op;

      //  DCACHE flush request
      //  {{{
      always_ff @(posedge clk_i or negedge rst_ni) begin : flush_ff
        if (!rst_ni) begin
          flush_fsm_q <= FLUSH_IDLE;
        end else begin
          flush_fsm_q <= flush_fsm_d;
        end
      end

      always_comb begin : flush_comb
        forward_flush = 1'b0;
        cva6_dcache_flush_ack_o = 1'b0;

        flush_fsm_d = flush_fsm_q;

        case (flush_fsm_q)
          FLUSH_IDLE: begin
            if (cva6_dcache_flush_i) begin
              forward_flush = 1'b1;
              if (hpdcache_req_ready_i) begin
                flush_fsm_d = FLUSH_PEND;
              end
            end
          end
          FLUSH_PEND: begin
            if (hpdcache_rsp_valid_i) begin
              if (hpdcache_rsp_i.tid == '0) begin
                cva6_dcache_flush_ack_o = 1'b1;
                flush_fsm_d = FLUSH_IDLE;
              end
            end
          end
          default: begin
          end
        endcase
      end
      //  }}}

      // CBO logic
      //  {{{
      always_comb begin : store_cmo_comb
        store_op = hpdcache_pkg::HPDCACHE_REQ_STORE;

        if (CVA6Cfg.RVZiCbom) begin
          case (cva6_req_i.cbo_op)
            ariane_pkg::CBO_INVAL: store_op = hpdcache_pkg::HPDCACHE_REQ_CMO_INVAL_NLINE;
            ariane_pkg::CBO_CLEAN: store_op = hpdcache_pkg::HPDCACHE_REQ_CMO_FLUSH_NLINE;
            ariane_pkg::CBO_FLUSH: store_op = hpdcache_pkg::HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE;
            default: ;  // store - above
          endcase
        end
      end
      //  }}}


      //  AMO logic
      //  {{{
      always_comb begin : amo_op_comb
        amo_addr = cva6_amo_req_i.operand_a;
        amo_addr_offset = amo_addr[0+:HPDcacheCfg.reqOffsetWidth];
        amo_tag = amo_addr[HPDcacheCfg.reqOffsetWidth+:HPDcacheCfg.tagWidth];
        unique case (cva6_amo_req_i.amo_op)
          ariane_pkg::AMO_LR:   amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_LR;
          ariane_pkg::AMO_SC:   amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_SC;
          ariane_pkg::AMO_SWAP: amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_SWAP;
          ariane_pkg::AMO_ADD:  amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_ADD;
          ariane_pkg::AMO_AND:  amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_AND;
          ariane_pkg::AMO_OR:   amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_OR;
          ariane_pkg::AMO_XOR:  amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_XOR;
          ariane_pkg::AMO_MAX:  amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_MAX;
          ariane_pkg::AMO_MAXU: amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_MAXU;
          ariane_pkg::AMO_MIN:  amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_MIN;
          ariane_pkg::AMO_MINU: amo_op = hpdcache_pkg::HPDCACHE_REQ_AMO_MINU;
          default:              amo_op = hpdcache_pkg::HPDCACHE_REQ_LOAD;
        endcase
      end
      //  }}}

      //  Request forwarding
      //  {{{
      assign hpdcache_req_is_uncacheable = !config_pkg::is_inside_cacheable_regions(
          CVA6Cfg,
          {
            {64 - CVA6Cfg.DCACHE_TAG_WIDTH{1'b0}}
            , hpdcache_req.addr_tag,
            {CVA6Cfg.DCACHE_INDEX_WIDTH{1'b0}}
          }
      );

      always_comb begin : generate_amo_inputs
        amo_data = '0;
        amo_data_be = '0;
        if (cva6_amo_req_i.size == 3'b000) begin
          amo_data = {{120{1'b0}}, cva6_amo_req_i.operand_b[0+:8]};
          amo_data_be = 16'h0001;
        end
        if (cva6_amo_req_i.size == 3'b001) begin
          amo_data = {{112{1'b0}}, cva6_amo_req_i.operand_b[0+:16]};
          amo_data_be = 16'h0003;
        end else begin
          amo_data = {{112{1'b0}}, {2{amo_data[0+:8]}}};
        end
        if (cva6_amo_req_i.size == 3'b010) begin
          amo_data = {{96{1'b0}}, cva6_amo_req_i.operand_b[0+:32]};
          amo_data_be = 16'h000f;
        end else begin
          amo_data = {{96{1'b0}}, {2{amo_data[0+:16]}}};
        end
        if (cva6_amo_req_i.size == 3'b011) begin
          amo_data = {{64{1'b0}}, cva6_amo_req_i.operand_b[0+:64]};
          amo_data_be = 16'h00ff;
        end else begin
          amo_data = {{64{1'b0}}, {2{amo_data[0+:32]}}};
        end
        if (CVA6Cfg.CheriPresent && cva6_amo_req_i.size == 3'b100) begin
          amo_data = cva6_amo_req_i.operand_b[0+:128];
          amo_data_be = 16'hffff;
        end else begin
          amo_data = {{2{amo_data[0+:64]}}};
        end
        amo_data_be = amo_data_be << (CVA6Cfg.CheriPresent ? cva6_amo_req_i.operand_a[3:0] : cva6_amo_req_i.operand_a[2:0]);
        amo_user = cva6_amo_req_i.size == 3'b100 && cva6_amo_req_i.cap_vld;
      end

      assign hpdcache_req_amo = '{
              addr_offset: amo_addr_offset,
              wdata: amo_data,
              wuser: amo_user,
              op: amo_op,
              be: amo_data_be,
              size: cva6_amo_req_i.size,
              sid: hpdcache_req_sid_i,
              tid: '1,
              need_rsp: 1'b1,
              phys_indexed: 1'b1,
              addr_tag: amo_tag,
              pma: '{
                  uncacheable: hpdcache_req_is_uncacheable,
                  io: 1'b0,
                  wr_policy_hint: hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO
              }
          };

      assign hpdcache_req_store = '{
              addr_offset: cva6_req_i.address_index,
              wdata: cva6_req_i.data_wdata,
              wuser: cva6_req_i.data_wuser,
              op: store_op,
              be: cva6_req_i.data_be,
              size: cva6_req_i.data_size,
              sid: hpdcache_req_sid_i,
              tid: '0,
              need_rsp:
              store_op
              !=
              hpdcache_pkg::HPDCACHE_REQ_STORE,  // CMO requests need a response
              phys_indexed: 1'b1,
              addr_tag: cva6_req_i.address_tag,
              pma: '{
                  uncacheable: hpdcache_req_is_uncacheable,
                  io: 1'b0,
                  wr_policy_hint: hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO
              }
          };

      assign hpdcache_req_flush = '{
              addr_offset: '0,
              addr_tag: '0,
              wdata: '0,
              wuser: '0,
              op:
              InvalidateOnFlush
              ?
              hpdcache_pkg::HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL
              :
              hpdcache_pkg::HPDCACHE_REQ_CMO_FLUSH_ALL,
              be: '0,
              size: '0,
              sid: hpdcache_req_sid_i,
              tid: '0,
              need_rsp: 1'b1,
              phys_indexed: 1'b0,
              pma: '{
                  uncacheable: 1'b0,
                  io: 1'b0,
                  wr_policy_hint: hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO
              }
          };

      assign forward_store = cva6_req_i.data_req;
      assign forward_amo = cva6_amo_req_i.req;

      assign hpdcache_req_valid_o = (forward_amo & ~amo_pending_q) | forward_store | forward_flush;

      assign hpdcache_req = forward_amo   ? hpdcache_req_amo :
                            forward_store ? hpdcache_req_store : hpdcache_req_flush;

      assign hpdcache_req_abort_o = 1'b0;  // unused on physically indexed requests
      assign hpdcache_req_tag_o = '0;  // unused on physically indexed requests
      assign hpdcache_req_pma_o.uncacheable = 1'b0;
      assign hpdcache_req_pma_o.io = 1'b0;
      assign hpdcache_req_pma_o.wr_policy_hint = hpdcache_pkg::HPDCACHE_WR_POLICY_AUTO;
      //  }}}

      //  Response forwarding
      //  {{{
      always_comb begin
        amo_resp = hpdcache_rsp_i.rdata[0];
        amo_resp_cap_vld = hpdcache_rsp_i.ruser;
        if (cva6_amo_req_i.size <= 3'b011) begin
          if (CVA6Cfg.CheriPresent && amo_addr[3] == 1'b1) begin
            amo_resp[63:0] = amo_resp[127:64];
          end
          amo_resp[127:64] = 64'b0;
          amo_resp_cap_vld = 1'b0;
        end
        if (cva6_amo_req_i.size <= 3'b010) begin
          if (amo_addr[2] == 1'b1) begin
            amo_resp[31:0] = amo_resp[63:32];
          end
          amo_resp[63:32] = {32{amo_resp[31]}};
        end
        if (cva6_amo_req_i.size <= 3'b001) begin
          if (amo_addr[1] == 1'b1) begin
            amo_resp[15:0] = amo_resp[31:16];
          end
          amo_resp[63:16] = {48{amo_resp[15]}};
        end
        if (cva6_amo_req_i.size == 3'b000) begin
          if (amo_addr[0] == 1'b1) begin
            amo_resp[7:0] = amo_resp[15:8];
          end
          amo_resp[63:8] = {56{amo_resp[7]}};
        end
      end

      assign cva6_req_o.data_rvalid = hpdcache_rsp_valid_i && (hpdcache_rsp_i.tid != '1);
      assign cva6_req_o.data_rdata = hpdcache_rsp_i.rdata;
      assign cva6_req_o.data_ruser = hpdcache_rsp_i.ruser;
      assign cva6_req_o.data_rid = hpdcache_rsp_i.tid;
      assign cva6_req_o.data_gnt = hpdcache_req_ready_i;

      assign cva6_amo_resp_o.ack = hpdcache_rsp_valid_i && (hpdcache_rsp_i.tid == '1);
      assign cva6_amo_resp_o.result = amo_resp;
      assign cva6_amo_resp_o.cap_vld = amo_resp_cap_vld;
      //  }}}

      always_ff @(posedge clk_i or negedge rst_ni) begin : amo_pending_ff
        if (!rst_ni) begin
          amo_pending_q <= 1'b0;
        end else begin
          amo_pending_q <=
              ( cva6_amo_req_i.req  & hpdcache_req_ready_i & ~amo_pending_q) |
              (~cva6_amo_resp_o.ack & amo_pending_q);
        end
      end

      //  Assertions
      //  {{{
      //    pragma translate_off
      forward_one_request_assert :
      assert property (@(posedge clk_i) disable iff (rst_ni !== 1'b1) ($onehot0(
          {forward_store, forward_amo, forward_flush}
      )))
      else $error("Only one request shall be forwarded");
      //    pragma translate_on
      //  }}}
    end
    //  }}}
  endgenerate

  assign hpdcache_req_o = hpdcache_req;
  //  }}}
endmodule
