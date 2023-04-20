// Copyright (c) 2022 ETH Zurich, University of Bologna
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
// Authors:
// - Tobias Senti <tsenti@ethz.ch>

`include "axi/assign.svh"
`include "common_cells/assertions.svh"

/// Splits a single read / write slave into one read and one write master
///
/// Connects the ar and r channel of the read / write slave to the read master
/// and the aw, w and b channel of the read / write slave to the write master
module axi_rw_split #(
  parameter type axi_req_t  = logic,
  parameter type axi_resp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  // Read / Write Slave
  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,

  // Read Master
  output axi_req_t  mst_read_req_o,
  input  axi_resp_t mst_read_resp_i,

  // Write Master
  output axi_req_t  mst_write_req_o,
  input  axi_resp_t mst_write_resp_i
);

  //--------------------------------------
  // Read channel data
  //--------------------------------------

  // Assign Read channel structs
  `AXI_ASSIGN_AR_STRUCT ( mst_read_req_o.ar  , slv_req_i.ar       )
  `AXI_ASSIGN_R_STRUCT  ( slv_resp_o.r       , mst_read_resp_i.r  )

  // Read AW and W channel data
  assign mst_read_req_o.aw        = '0;
  assign mst_read_req_o.w         = '0;


  //--------------------------------------
  // Read channel handshakes
  //--------------------------------------

  // Read AR channel handshake
  assign mst_read_req_o.ar_valid  = slv_req_i.ar_valid;
  assign slv_resp_o.ar_ready      = mst_read_resp_i.ar_ready;

  // Read R channel handshake
  assign slv_resp_o.r_valid       = mst_read_resp_i.r_valid;
  assign mst_read_req_o.r_ready   = slv_req_i.r_ready;

  // Read AW, W and B handshake
  assign mst_read_req_o.aw_valid  = 1'b0;
  assign mst_read_req_o.w_valid   = 1'b0;
  assign mst_read_req_o.b_ready   = 1'b0;

  // check for B never to be valid
  `ASSERT_NEVER(mst_read_resp_b_valid, mst_read_resp_i.b_valid, clk_i, !rst_ni)


  //--------------------------------------
  // Write channel data
  //--------------------------------------

  // Assign Write channel structs
  `AXI_ASSIGN_AW_STRUCT ( mst_write_req_o.aw , slv_req_i.aw       )
  `AXI_ASSIGN_W_STRUCT  ( mst_write_req_o.w  , slv_req_i.w        )
  `AXI_ASSIGN_B_STRUCT  ( slv_resp_o.b       , mst_write_resp_i.b )

  // Write AR channel data
  assign mst_write_req_o.ar       = '0;


  //--------------------------------------
  // Write channel handshakes
  //--------------------------------------

  // Write AR and R channel handshake
  assign mst_write_req_o.ar_valid = 1'b0;
  assign mst_write_req_o.r_ready  = 1'b0;

  // check for R never to be valid
  `ASSERT_NEVER(mst_read_resp_r_valid, mst_read_resp_i.r_valid, clk_i, !rst_ni)

  // Write AW channel handshake
  assign mst_write_req_o.aw_valid = slv_req_i.aw_valid;
  assign slv_resp_o.aw_ready      = mst_write_resp_i.aw_ready;

  // Write W channel handshake
  assign mst_write_req_o.w_valid  = slv_req_i.w_valid;
  assign slv_resp_o.w_ready       = mst_write_resp_i.w_ready;

  // Write B channel handshake
  assign slv_resp_o.b_valid       = mst_write_resp_i.b_valid;
  assign mst_write_req_o.b_ready  = slv_req_i.b_ready;

endmodule : axi_rw_split
