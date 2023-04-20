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

/// Joins a read and a write slave into one single read / write master
///
/// Connects the ar and r channel of the read slave to the read / write master
/// and the aw, w and b channel of the write slave to the read / write master
module axi_rw_join #(
  parameter type axi_req_t  = logic,
  parameter type axi_resp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  // Read Slave
  input  axi_req_t  slv_read_req_i,
  output axi_resp_t slv_read_resp_o,

  // Write Slave
  input  axi_req_t  slv_write_req_i,
  output axi_resp_t slv_write_resp_o,

  // Read / Write Master
  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i
);

  //--------------------------------------
  // Read channel data
  //--------------------------------------

  // Assign Read Structs
  `AXI_ASSIGN_AR_STRUCT ( mst_req_o.ar       , slv_read_req_i.ar  )
  `AXI_ASSIGN_R_STRUCT  ( slv_read_resp_o.r  , mst_resp_i.r       )

  // Read B channel data
  assign slv_read_resp_o.b         = '0;


  //--------------------------------------
  // Read channel handshakes
  //--------------------------------------

  // Read AR channel handshake
  assign mst_req_o.ar_valid        = slv_read_req_i.ar_valid;
  assign slv_read_resp_o.ar_ready  = mst_resp_i.ar_ready;

  // Read R channel handshake
  assign slv_read_resp_o.r_valid   = mst_resp_i.r_valid;
  assign mst_req_o.r_ready         = slv_read_req_i.r_ready;

  // Read AW, W and B handshake
  assign slv_read_resp_o.aw_ready  = 1'b0;
  assign slv_read_resp_o.w_ready   = 1'b0;
  assign slv_read_resp_o.b_valid   = 1'b0;

  // check for AW and W never to be valid
  `ASSERT_NEVER(slv_read_req_aw_valid, slv_read_req_i.aw_valid, clk_i, !rst_ni)
  `ASSERT_NEVER(slv_read_req_w_valid,  slv_read_req_i.w_valid,  clk_i, !rst_ni)

  //--------------------------------------
  // Write channel data
  //--------------------------------------

  // Assign Write Structs
  `AXI_ASSIGN_AW_STRUCT ( mst_req_o.aw       , slv_write_req_i.aw )
  `AXI_ASSIGN_W_STRUCT  ( mst_req_o.w        , slv_write_req_i.w  )
  `AXI_ASSIGN_B_STRUCT  ( slv_write_resp_o.b , mst_resp_i.b       )

  // Write R channel data
  assign slv_write_resp_o.r        = '0;


  //--------------------------------------
  // Write channel handshakes
  //--------------------------------------

  // Write AR and R channel handshake
  assign slv_write_resp_o.ar_ready = 1'b0;
  assign slv_write_resp_o.r_valid  = 1'b0;

  // check for AR to never be valid
  `ASSERT_NEVER(slv_write_req_ar_valid, slv_write_req_i.ar_valid, clk_i, !rst_ni)

  // Write AW channel handshake
  assign mst_req_o.aw_valid        = slv_write_req_i.aw_valid;
  assign slv_write_resp_o.aw_ready = mst_resp_i.aw_ready;

  // Write W channel handshake
  assign mst_req_o.w_valid         = slv_write_req_i.w_valid;
  assign slv_write_resp_o.w_ready  = mst_resp_i.w_ready;

  // Write B channel handshake
  assign slv_write_resp_o.b_valid  = mst_resp_i.b_valid;
  assign mst_req_o.b_ready         = slv_write_req_i.b_ready;

endmodule : axi_rw_join
