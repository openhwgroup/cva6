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
// Andreas Kurth  <akurth@iis.ee.ethz.ch>


// A connector that allows addresses of AXI requests to be changed.
module axi_modify_address #(
  parameter type slv_addr_t = logic, // address type of slave port
  parameter type  slv_req_t = logic, // request type slave port
  parameter type slv_resp_t = logic, // response type slave port
  parameter type mst_addr_t = logic, // address type of master port
  parameter type  mst_req_t = logic, // request type master port
  parameter type mst_resp_t = logic  // response type master port
) (
  // slave port
  input  slv_req_t  slv_req_i,
  output slv_resp_t slv_resp_o,
  output slv_addr_t slv_aw_addr_o,
  output slv_addr_t slv_ar_addr_o,
  // master port
  output mst_req_t  mst_req_o,
  input  mst_resp_t mst_resp_i,
  input  mst_addr_t mst_aw_addr_i,
  input  mst_addr_t mst_ar_addr_i
);
  assign slv_aw_addr_o = slv_req_i.aw.addr;
  assign slv_ar_addr_o = slv_req_i.ar.addr;

  assign mst_req_o = '{
    aw: '{
      id:     slv_req_i.aw.id,
      addr:   mst_aw_addr_i,
      len:    slv_req_i.aw.len,
      size:   slv_req_i.aw.size,
      burst:  slv_req_i.aw.burst,
      lock:   slv_req_i.aw.lock,
      cache:  slv_req_i.aw.cache,
      prot:   slv_req_i.aw.prot,
      qos:    slv_req_i.aw.qos,
      region: slv_req_i.aw.region,
      atop:   slv_req_i.aw.atop,
      user:   slv_req_i.aw.user,
      default: '0
    },
    aw_valid: slv_req_i.aw_valid,
    w:        slv_req_i.w,
    b_ready:  slv_req_i.b_ready,
    ar: '{
      id:     slv_req_i.ar.id,
      addr:   mst_ar_addr_i,
      len:    slv_req_i.ar.len,
      size:   slv_req_i.ar.size,
      burst:  slv_req_i.ar.burst,
      lock:   slv_req_i.ar.lock,
      cache:  slv_req_i.ar.cache,
      prot:   slv_req_i.ar.prot,
      qos:    slv_req_i.ar.qos,
      region: slv_req_i.ar.region,
      user:   slv_req_i.ar.user,
      default: '0
    },
    ar_valid: slv_req_i.ar_valid,
    r_ready:  slv_req_i.r_ready,
    default: '0
  };

  assign slv_resp_o = mst_resp_i;
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"

// interface wrapper
module axi_modify_address_intf #(
  parameter int ADDR_WIDTH_IN  = -1,
  parameter int ADDR_WIDTH_OUT = ADDR_WIDTH_IN
) (
  AXI_BUS.Slave   in,
  AXI_BUS.Master  out,
  output logic [ADDR_WIDTH_IN-1:0]  aw_addr_in,
  output logic [ADDR_WIDTH_IN-1:0]  ar_addr_in,
  input  logic [ADDR_WIDTH_OUT-1:0] aw_addr_out,
  input  logic [ADDR_WIDTH_OUT-1:0] ar_addr_out
);

  localparam int unsigned ID_WIDTH   = $bits(in.aw_id);
  localparam int unsigned DATA_WIDTH = $bits(in.w_data);
  localparam int unsigned USER_WIDTH = $bits(in.aw_user);

  typedef logic [ID_WIDTH-1:0]       id_t;
  typedef logic [ADDR_WIDTH_IN-1:0]  slv_addr_t;
  typedef logic [ADDR_WIDTH_OUT-1:0] mst_addr_t;
  typedef logic [DATA_WIDTH-1:0]     data_t;
  typedef logic [DATA_WIDTH/8-1:0]   strb_t;
  typedef logic [USER_WIDTH-1:0]     user_t;

  `AXI_TYPEDEF_AW_CHAN_T ( slv_aw_chan_t, slv_addr_t, id_t, user_t )
  `AXI_TYPEDEF_AW_CHAN_T ( mst_aw_chan_t, mst_addr_t, id_t, user_t )
  `AXI_TYPEDEF_W_CHAN_T  (  w_chan_t, data_t,       strb_t, user_t )
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_t,         id_t,         user_t )
  `AXI_TYPEDEF_AR_CHAN_T ( slv_ar_chan_t, slv_addr_t, id_t, user_t )
  `AXI_TYPEDEF_AR_CHAN_T ( mst_ar_chan_t, mst_addr_t, id_t, user_t )
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_t, data_t, id_t,         user_t )
  `AXI_TYPEDEF_REQ_T     (  slv_req_t, slv_aw_chan_t, w_chan_t, slv_ar_chan_t )
  `AXI_TYPEDEF_REQ_T     (  mst_req_t, mst_aw_chan_t, w_chan_t, mst_ar_chan_t )
  `AXI_TYPEDEF_RESP_T    (     resp_t,  b_chan_t, r_chan_t            )

  slv_req_t  slv_req;
  mst_req_t  mst_req;
  resp_t     slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ    ( slv_req, in       )
  `AXI_ASSIGN_FROM_RESP ( in,      slv_resp )

  `AXI_ASSIGN_FROM_REQ  ( out     , mst_req )
  `AXI_ASSIGN_TO_RESP   ( mst_resp, out     )

  axi_modify_address #(
    .slv_addr_t ( slv_req_t  ), // address type of slave port
    .slv_req_t  ( resp_t     ), // request type slave port
    .slv_resp_t ( slv_addr_t ), // response type slave port
    .mst_addr_t ( mst_req_t  ), // address type of master port
    .mst_req_t  ( resp_t     ), // request type master port
    .mst_resp_t ( mst_addr_t )  // response type master port
  ) i_axi_modify_address (
  // slave port
    .slv_req_i     ( slv_req     ),
    .slv_resp_o    ( slv_resp    ),
    .slv_aw_addr_o ( aw_addr_in  ),
    .slv_ar_addr_o ( ar_addr_in  ),
  // master port
    .mst_req_o     ( mst_req     ),
    .mst_resp_i    ( mst_resp    ),
    .mst_aw_addr_i ( aw_addr_out ),
    .mst_ar_addr_i ( ar_addr_out )
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert(ADDR_WIDTH_IN > 0);
    assert(ADDR_WIDTH_OUT > 0);
  end
`endif
// pragma translate_on
endmodule
