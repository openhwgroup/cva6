// Copyright 2018 ETH Zurich and University of Bologna.
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

/// A protocol converter from AXI4 to a register interface.

`include "axi/typedef.svh"

module axi_to_reg #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1,
  /// The width of the data.
  parameter int DATA_WIDTH = -1,
  /// The width of the id.
  parameter int ID_WIDTH = -1,
  /// The width of the user signal.
  parameter int USER_WIDTH = -1,
  /// Whether the AXI-Lite W channel should be decoupled with a register. This
  /// can help break long paths at the expense of registers.
  parameter bit DECOUPLE_W = 1,
  /// AXI request struct type.
  parameter type axi_req_t = logic,
  /// AXI response struct type.
  parameter type axi_rsp_t = logic,
  /// Regbus request struct type.
  parameter type reg_req_t = logic,
  /// Regbus response struct type.
  parameter type reg_rsp_t = logic
)(
  input  logic  clk_i             ,
  input  logic  rst_ni            ,
  input  logic  testmode_i        ,
  input  axi_req_t  axi_lite_req_i,
  output axi_rsp_t  axi_lite_rsp_o,
  output reg_req_t  reg_req_o     ,
  input  reg_rsp_t  reg_rsp_i
);

  typedef logic [ADDR_WIDTH-1:0] addr_t;
  typedef logic [DATA_WIDTH-1:0] data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_lite_resp_t, b_chan_t, r_chan_t)

  axi_lite_req_t axi_lite_req;
  axi_lite_resp_t axi_lite_resp;

  //  convert axi to axi-lite
  axi_to_axi_lite #(
    .AxiAddrWidth     ( ADDR_WIDTH ),
    .AxiDataWidth     ( DATA_WIDTH ),
    .AxiIdWidth       ( ID_WIDTH   ),
    .AxiUserWidth     ( USER_WIDTH ),
    /// Maximum number of outstanding writes.
    .AxiMaxWriteTxns ( 2 ),
    /// Maximum number of outstanding reads.
    .AxiMaxReadTxns  ( 2 ),
    .FallThrough     ( 0 ),
    .full_req_t      ( axi_req_t ),
    .full_resp_t     ( axi_rsp_t ),
    .lite_req_t      ( axi_lite_req_t ),
    .lite_resp_t     ( axi_lite_resp_t )
  ) i_axi_to_axi_lite (
    .clk_i,
    .rst_ni,
    .test_i ( testmode_i ),
    .slv_req_i (axi_lite_req_i),
    .slv_resp_o (axi_lite_rsp_o),
    .mst_req_o (axi_lite_req),
    .mst_resp_i (axi_lite_resp)
  );

  axi_lite_to_reg #(
    /// The width of the address.
    .ADDR_WIDTH ( ADDR_WIDTH ),
    /// The width of the data.
    .DATA_WIDTH ( DATA_WIDTH ),
    /// Whether the AXI-Lite W channel should be decoupled with a register. This
    /// can help break long paths at the expense of registers.
    .DECOUPLE_W ( DECOUPLE_W ),
    .axi_lite_req_t ( axi_lite_req_t ),
    .axi_lite_rsp_t ( axi_lite_resp_t ),
    .reg_req_t (reg_req_t),
    .reg_rsp_t (reg_rsp_t)
  ) i_axi_lite_to_reg (
    .clk_i,
    .rst_ni,
    .axi_lite_req_i (axi_lite_req),
    .axi_lite_rsp_o (axi_lite_resp),
    .reg_req_o,
    .reg_rsp_i
  );

endmodule


