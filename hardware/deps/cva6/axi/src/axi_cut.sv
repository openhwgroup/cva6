// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

import axi_pkg::*;


/// An AXI4 cut.
///
/// Breaks all combinatorial paths between its input and output.
module axi_cut #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The data width.
  parameter int DATA_WIDTH = -1,
  /// The ID width.
  parameter int ID_WIDTH = -1,
  // The user data width.
  parameter int USER_WIDTH = -1
)(
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_BUS.Slave   in     ,
  AXI_BUS.Master  out
);

  localparam STRB_WIDTH = DATA_WIDTH / 8;

  typedef logic [ID_WIDTH-1:0]   id_t;
  typedef logic [ADDR_WIDTH-1:0] addr_t;
  typedef logic [DATA_WIDTH-1:0] data_t;
  typedef logic [STRB_WIDTH-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0] user_t;

  // Check the invariants.
  `ifndef VCS
  `ifndef SYNTHESIS
  initial begin
    assert(ADDR_WIDTH >= 0);
    assert(DATA_WIDTH >= 0);
    assert(ID_WIDTH >= 0);
    assert(USER_WIDTH >= 0);
    assert(in.AXI_ADDR_WIDTH == ADDR_WIDTH);
    assert(in.AXI_DATA_WIDTH == DATA_WIDTH);
    assert(in.AXI_ID_WIDTH == ID_WIDTH);
    assert(in.AXI_USER_WIDTH == USER_WIDTH);
    assert(out.AXI_ADDR_WIDTH == ADDR_WIDTH);
    assert(out.AXI_DATA_WIDTH == DATA_WIDTH);
    assert(out.AXI_ID_WIDTH == ID_WIDTH);
    assert(out.AXI_USER_WIDTH == USER_WIDTH);
  end
  `endif
  `endif

  // Create spill registers to buffer each channel.
  typedef struct packed {
    id_t        id;
    addr_t      addr;
    logic [7:0] len;
    logic [2:0] size;
    burst_t     burst;
    logic       lock;
    cache_t     cache;
    prot_t      prot;
    qos_t       qos;
    region_t    region;
    logic [5:0] atop;   // Only defined on the AW channel.
    user_t      user;
  } channel_ax_t;

  typedef struct packed {
    data_t data;
    strb_t strb;
    logic  last;
    user_t user;
  } channel_w_t;

  typedef struct packed {
    id_t   id;
    resp_t resp;
    user_t user;
  } channel_b_t;

  typedef struct packed {
    id_t   id;
    data_t data;
    resp_t resp;
    logic  last;
    user_t user;
  } channel_r_t;

  channel_ax_t aw_in, aw_out;
  assign aw_in.id      = in.aw_id      ;
  assign aw_in.addr    = in.aw_addr    ;
  assign aw_in.len     = in.aw_len     ;
  assign aw_in.size    = in.aw_size    ;
  assign aw_in.burst   = in.aw_burst   ;
  assign aw_in.lock    = in.aw_lock    ;
  assign aw_in.cache   = in.aw_cache   ;
  assign aw_in.prot    = in.aw_prot    ;
  assign aw_in.qos     = in.aw_qos     ;
  assign aw_in.region  = in.aw_region  ;
  assign aw_in.atop    = in.aw_atop    ;
  assign aw_in.user    = in.aw_user    ;
  assign out.aw_id     = aw_out.id     ;
  assign out.aw_addr   = aw_out.addr   ;
  assign out.aw_len    = aw_out.len    ;
  assign out.aw_size   = aw_out.size   ;
  assign out.aw_burst  = aw_out.burst  ;
  assign out.aw_lock   = aw_out.lock   ;
  assign out.aw_cache  = aw_out.cache  ;
  assign out.aw_prot   = aw_out.prot   ;
  assign out.aw_qos    = aw_out.qos    ;
  assign out.aw_region = aw_out.region ;
  assign out.aw_atop   = aw_out.atop   ;
  assign out.aw_user   = aw_out.user   ;
  spill_register #(.T(channel_ax_t)) i_reg_aw (
    .clk_i   ( clk_i        ),
    .rst_ni  ( rst_ni       ),
    .valid_i ( in.aw_valid  ),
    .ready_o ( in.aw_ready  ),
    .data_i  ( aw_in        ),
    .valid_o ( out.aw_valid ),
    .ready_i ( out.aw_ready ),
    .data_o  ( aw_out       )
  );

  channel_w_t w_in, w_out;
  assign w_in.data  = in.w_data  ;
  assign w_in.strb  = in.w_strb  ;
  assign w_in.last  = in.w_last  ;
  assign w_in.user  = in.w_user  ;
  assign out.w_data = w_out.data ;
  assign out.w_strb = w_out.strb ;
  assign out.w_last = w_out.last ;
  assign out.w_user = w_out.user ;
  spill_register #(.T(channel_w_t)) i_reg_w (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .valid_i ( in.w_valid  ),
    .ready_o ( in.w_ready  ),
    .data_i  ( w_in        ),
    .valid_o ( out.w_valid ),
    .ready_i ( out.w_ready ),
    .data_o  ( w_out       )
  );

  channel_b_t b_in, b_out;
  assign b_out.id   = out.b_id   ;
  assign b_out.resp = out.b_resp ;
  assign b_out.user = out.b_user ;
  assign in.b_id    = b_in.id    ;
  assign in.b_resp  = b_in.resp  ;
  assign in.b_user  = b_in.user  ;
  spill_register #(.T(channel_b_t)) i_reg_b (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .valid_i ( out.b_valid ),
    .ready_o ( out.b_ready ),
    .data_i  ( b_out       ),
    .valid_o ( in.b_valid  ),
    .ready_i ( in.b_ready  ),
    .data_o  ( b_in        )
  );

  channel_ax_t ar_in, ar_out;
  assign ar_in.id      = in.ar_id      ;
  assign ar_in.addr    = in.ar_addr    ;
  assign ar_in.len     = in.ar_len     ;
  assign ar_in.size    = in.ar_size    ;
  assign ar_in.burst   = in.ar_burst   ;
  assign ar_in.lock    = in.ar_lock    ;
  assign ar_in.cache   = in.ar_cache   ;
  assign ar_in.prot    = in.ar_prot    ;
  assign ar_in.qos     = in.ar_qos     ;
  assign ar_in.region  = in.ar_region  ;
  assign ar_in.atop    = 'X            ; // Not defined on the AR channel.
  assign ar_in.user    = in.ar_user    ;
  assign out.ar_id     = ar_out.id     ;
  assign out.ar_addr   = ar_out.addr   ;
  assign out.ar_len    = ar_out.len    ;
  assign out.ar_size   = ar_out.size   ;
  assign out.ar_burst  = ar_out.burst  ;
  assign out.ar_lock   = ar_out.lock   ;
  assign out.ar_cache  = ar_out.cache  ;
  assign out.ar_prot   = ar_out.prot   ;
  assign out.ar_qos    = ar_out.qos    ;
  assign out.ar_region = ar_out.region ;
  assign out.ar_user   = ar_out.user   ;
  spill_register #(.T(channel_ax_t)) i_reg_ar (
    .clk_i   ( clk_i        ),
    .rst_ni  ( rst_ni       ),
    .valid_i ( in.ar_valid  ),
    .ready_o ( in.ar_ready  ),
    .data_i  ( ar_in        ),
    .valid_o ( out.ar_valid ),
    .ready_i ( out.ar_ready ),
    .data_o  ( ar_out       )
  );

  channel_r_t r_in, r_out;
  assign r_out.id   = out.r_id   ;
  assign r_out.data = out.r_data ;
  assign r_out.resp = out.r_resp ;
  assign r_out.last = out.r_last ;
  assign r_out.user = out.r_user ;
  assign in.r_id    = r_in.id    ;
  assign in.r_data  = r_in.data  ;
  assign in.r_resp  = r_in.resp  ;
  assign in.r_last  = r_in.last  ;
  assign in.r_user  = r_in.user  ;
  spill_register #(.T(channel_r_t)) i_reg_r (
    .clk_i   ( clk_i       ),
    .rst_ni  ( rst_ni      ),
    .valid_i ( out.r_valid ),
    .ready_o ( out.r_ready ),
    .data_i  ( r_out       ),
    .valid_o ( in.r_valid  ),
    .ready_i ( in.r_ready  ),
    .data_o  ( r_in        )
  );

endmodule
