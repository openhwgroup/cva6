/*
 *  Copyright 2023 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : July, 2023
 *  Description   : Interface adapter for the load port from the CVA6 core
 *  History       :
 */
module cva6_hpdcache_load_if_adapter
//  Parameters
//  {{{
#(
    parameter ariane_pkg::ariane_cfg_t ArianeCfg = ariane_pkg::ArianeDefaultConfig
)
//  }}}

//  Ports
//  {{{
(
  //  Clock and active-low reset pins
  input  logic                            clk_i,
  input  logic                            rst_ni,

  //  Port ID
  input  hpdcache_pkg::hpdcache_req_sid_t dcache_req_sid_i,

  //  Request/response ports from/to the CVA6 core
  input  ariane_pkg::dcache_req_i_t       cva6_req_i,
  output ariane_pkg::dcache_req_o_t       cva6_req_o,

  //  Request port to the L1 Dcache
  output logic                            dcache_req_valid_o,
  input  logic                            dcache_req_ready_i,
  output hpdcache_pkg::hpdcache_req_t     dcache_req_o,
  output logic                            dcache_req_abort_o,
  output hpdcache_pkg::hpdcache_tag_t     dcache_req_tag_o,
  output hpdcache_pkg::hpdcache_pma_t     dcache_req_pma_o,

  //  Response port from the L1 Dcache
  input  logic                            dcache_rsp_valid_i,
  input  hpdcache_pkg::hpdcache_rsp_t     dcache_rsp_i
);
//  }}}

  //  Internal nets and registers
  //  {{{
  struct packed {
      logic [ariane_pkg::DCACHE_INDEX_WIDTH-1:0]   address_index;
      logic [(riscv::XLEN/8)-1:0]                  data_be;
      logic [1:0]                                  data_size;
      logic [ariane_pkg::DCACHE_TID_WIDTH-1:0]     data_id;
      logic [hpdcache_pkg::HPDCACHE_TAG_WIDTH-1:0] address_tag;
  } ldbuf_q;

  struct packed {
      riscv::xlen_t                                rdata;
      logic [ariane_pkg::DCACHE_TID_WIDTH-1:0]     tid;
  } ldbuf_rsp_q;

  enum {
    LOAD_IDLE,
    LOAD_TAG,
    LOAD_WAIT_GNT,
    LOAD_PEND_RSP
  } load_state_q, load_state_d;

  logic [hpdcache_pkg::HPDCACHE_TAG_WIDTH-1:0] dcache_req_tag;
  logic ldbuf_req_we;
  logic ldbuf_tag_we, ldbuf_tag_sel;
  logic ldbuf_rsp_we;
  logic ldbuf_rsp_sel, ldbuf_rsp_abort_sel;

  logic cva6_req_ready;
  logic cva6_rsp_valid;
  //  }}}

  //  Core request grant control
  //  {{{
  //  }}}

  //  Buffer for load requests
  //  {{{
  always_ff @(posedge clk_i)
  begin : ldbuf_ff
    if (ldbuf_req_we) begin
      ldbuf_q.address_index <= cva6_req_i.address_index;
      ldbuf_q.data_be <= cva6_req_i.data_be;
      ldbuf_q.data_size <= cva6_req_i.data_size;
      ldbuf_q.data_id <= cva6_req_i.data_id;
    end

    if (ldbuf_tag_we) begin
      ldbuf_q.address_tag <= cva6_req_i.address_tag;
    end
  end
  //  }}}

  //  Buffer for load responses
  //  {{{
  always_ff @(posedge clk_i)
  begin : ldbuf_rsp_ff
    if (ldbuf_rsp_we) begin
      ldbuf_rsp_q.rdata <= dcache_rsp_i.rdata;
      ldbuf_rsp_q.tid <= dcache_rsp_i.tid;
    end
  end
  //  }}}

  //  CVA6 Load Request and HPDcache Response Processing
  //  {{{
  always_comb
  begin : load_fsm_comb
    ldbuf_req_we = 1'b0;
    ldbuf_tag_we = 1'b0;
    ldbuf_tag_sel = 1'b0;

    ldbuf_rsp_we = 1'b0;
    ldbuf_rsp_sel = 1'b0;
    ldbuf_rsp_abort_sel = 1'b0;

    dcache_req_valid_o = 1'b0;

    cva6_req_ready = 1'b0;
    cva6_rsp_valid = 1'b0;

    load_state_d = load_state_q;

    case (load_state_q)
      LOAD_IDLE: begin
        //  consume the request from the core
        cva6_req_ready = 1'b1;

        //  forward a response to the core from the HPDcache, if any
        cva6_rsp_valid = dcache_rsp_valid_i;

        //  new request from the CVA6
        if (cva6_req_i.data_req) begin
          //  store the request into the internal buffer
          ldbuf_req_we = 1'b1;

          //  wait for the tag on the next cycle
          load_state_d = LOAD_TAG;
        end
      end
      LOAD_TAG: begin
        //  if the request is not being aborted
        if (!cva6_req_i.kill_req) begin
          //  consume a new request from the core if the cache accepts the
          //  pending one
          cva6_req_ready = dcache_req_ready_i;

          //  forward the request to the cache
          dcache_req_valid_o = 1'b1;

          //  forward a response to the core from the HPDcache, if any
          cva6_rsp_valid = dcache_rsp_valid_i;

          //  if the cache is ready to accept a new request
          if (dcache_req_ready_i) begin
            //  if there is a new request from the core
            if (cva6_req_i.data_req) begin
              //  store the new request into the internal buffer
              ldbuf_req_we = 1'b1;

              //  keep the state to forward the tag of the new request in the
              //  next cycle
              load_state_d = LOAD_TAG;

            //  there is no new request from the core
            end else begin
              load_state_d = LOAD_IDLE;
            end

          //  the cache is not yet ready to accept a request
          end else begin
            //  store the request tag into the internal buffer
            ldbuf_tag_we = 1'b1;

            //  wait until the ready signal from the cache
            load_state_d = LOAD_WAIT_GNT;
          end

        //  the request is being aborted
        end else begin
          //  send a response for the aborted request
          cva6_rsp_valid = 1'b1;

          //  select metadata from the aborted request
          ldbuf_rsp_abort_sel = 1'b1;

          //  there is a pending response from the cache
          if (dcache_rsp_valid_i) begin
            //  save the response from the cache
            ldbuf_rsp_we = 1'b1;

            //  send the response from the cache on the next cycle as this
            //  module is currently responding to the aborted request
            load_state_d = LOAD_PEND_RSP;

          // there is no pending response from the cache
          end else begin
            load_state_d = LOAD_IDLE;
          end
        end
      end
      LOAD_WAIT_GNT: begin
        //  forward a response to the core from the HPDcache, if any
        cva6_rsp_valid = dcache_rsp_valid_i;

        //  forward the buffered request to the cache
        dcache_req_valid_o = 1'b1;

        //  select the buffered tag
        ldbuf_tag_sel = 1'b1;

        //  accept a new request if the cache consumes the pending one
        cva6_req_ready = dcache_req_ready_i;

        if (dcache_req_ready_i) begin
          //  there is a new request
          if (cva6_req_i.data_req) begin
            //  store the new request into the internal buffer
            ldbuf_req_we = 1'b1;

            //  wait for the tag on the next cycle
            load_state_d = LOAD_TAG;

          //  there is no new request
          end else begin
            load_state_d = LOAD_IDLE;
          end

        //  the cache cannot accept yet the pending request
        end else begin
          load_state_d = LOAD_WAIT_GNT;
        end
      end
      LOAD_PEND_RSP: begin
        //  forward the buffered response to the core
        cva6_rsp_valid = 1'b1;

        //  select the buffered response
        ldbuf_rsp_sel = 1'b1;

        //  there is a new response from the cache
        if (dcache_rsp_valid_i) begin
          //  save the response from the cache as this module is sending the
          //  previous one in this cycle
          ldbuf_rsp_we = 1'b1;

          load_state_d = LOAD_PEND_RSP;
        end else begin
          //  consume the request from the core, if any
          cva6_req_ready = 1'b1;

          if (cva6_req_i.data_req) begin
            load_state_d = LOAD_TAG;
          end else begin
            load_state_d = LOAD_IDLE;
          end
        end
      end
      default: begin
        // pragma translate_off
        $error("invalid state");
        // pragma translate_on
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni)
  begin : load_fsm_ff
    if (!rst_ni) begin
      load_state_q <= LOAD_IDLE;
    end else begin
      load_state_q <= load_state_d;
    end
  end

  //  LOAD request
  //  {{{
  assign dcache_req_tag = ldbuf_tag_sel ? ldbuf_q.address_tag : cva6_req_i.address_tag,
         dcache_req_o.addr_offset = ldbuf_q.address_index,
         dcache_req_o.wdata = '0,
         dcache_req_o.op = hpdcache_pkg::HPDCACHE_REQ_LOAD,
         dcache_req_o.be = ldbuf_q.data_be,
         dcache_req_o.size = ldbuf_q.data_size,
         dcache_req_o.sid = dcache_req_sid_i,
         dcache_req_o.tid = ldbuf_q.data_id,
         dcache_req_o.need_rsp = 1'b1,
         dcache_req_o.phys_indexed = 1'b1,
         dcache_req_o.addr_tag     = dcache_req_tag,
         dcache_req_o.pma.io       = 1'b0, 
         dcache_req_abort_o = 1'b0,  // unused on physically indexed requests
         dcache_req_tag_o = '0,  // unused on physically indexed requests
         dcache_req_pma_o = '0;  // unused on physically indexed requests

  assign dcache_req_o.pma.uncacheable =
      ~ariane_pkg::is_inside_cacheable_regions(ArianeCfg,
      { {{64-ariane_pkg::DCACHE_TAG_WIDTH}{1'b0}}, dcache_req_o.addr_tag,{ariane_pkg::DCACHE_INDEX_WIDTH{1'b0}}});
  //  }}}

  //  Response forwarding
  //  FIXME there is no error signal in the cva6 response interface to forward errors from memory
  //  {{{
  riscv::xlen_t                            cva6_rsp_rdata;
  logic [ariane_pkg::DCACHE_TID_WIDTH-1:0] cva6_rsp_rid;

  assign cva6_rsp_rdata = ldbuf_rsp_sel ? ldbuf_rsp_q.rdata : riscv::xlen_t'(dcache_rsp_i.rdata),
         cva6_rsp_rid = ldbuf_rsp_sel ? ldbuf_rsp_q.tid : dcache_rsp_i.tid;

  assign cva6_req_o.data_rvalid = cva6_rsp_valid,
         cva6_req_o.data_rdata = ldbuf_rsp_abort_sel ? '0 : cva6_rsp_rdata,
         cva6_req_o.data_rid = ldbuf_rsp_abort_sel ? ldbuf_q.data_id : cva6_rsp_rid,
         cva6_req_o.data_gnt = cva6_req_ready;
  //  }}}

  //  Assertions
  //  {{{
  //    pragma translate_off
  kill_and_tag_assert: assert property (@(posedge clk_i)
      cva6_req_i.kill_req |-> cva6_req_i.tag_valid) else
      $error("kill_req=1 shall be accompanied with tag_valid=1");
  no_valid_tag_or_kill_on_tag_assert: assert property (@(posedge clk_i)
      (load_state_q == LOAD_TAG) |-> (cva6_req_i.tag_valid | cva6_req_i.kill_req)) else
      $error("Expected tag or kill while on TAG");
  //    pragma translate_on
  //  }}}

endmodule