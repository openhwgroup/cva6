// Copyright (c) 2014-2019 ETH Zurich, University of Bologna
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
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Stefan Mach <smach@iis.ee.ethz.ch>

// Multiple AXI4 cuts.
//
// These can be used to relax timing pressure on very long AXI busses.
module axi_multicut #(
  parameter int unsigned NoCuts = 32'd1, // Number of cuts.
  // AXI channel structs
  parameter type aw_chan_t = logic,
  parameter type  w_chan_t = logic,
  parameter type  b_chan_t = logic,
  parameter type ar_chan_t = logic,
  parameter type  r_chan_t = logic,
  // AXI request & response structs
  parameter type     req_t = logic,
  parameter type    resp_t = logic
) (
  input  logic  clk_i,   // Clock
  input  logic  rst_ni,  // Asynchronous reset active low
  // slave port
  input  req_t  slv_req_i,
  output resp_t slv_resp_o,
  // master port
  output req_t  mst_req_o,
  input  resp_t mst_resp_i
);

  if (NoCuts == '0) begin : gen_no_cut
    // degenerate case, connect input to output
    assign mst_req_o  = slv_req_i;
    assign slv_resp_o = mst_resp_i;
  end else begin : gen_axi_cut
    // instantiate all needed cuts
    req_t  [NoCuts:0] cut_req;
    resp_t [NoCuts:0] cut_resp;

    // connect slave to the lowest index
    assign cut_req[0] = slv_req_i;
    assign slv_resp_o = cut_resp[0];

    // AXI cuts
    for (genvar i = 0; i < NoCuts; i++) begin : gen_axi_cuts
      axi_cut #(
        .Bypass    (      1'b0 ),
        .aw_chan_t ( aw_chan_t ),
        .w_chan_t  (  w_chan_t ),
        .b_chan_t  (  b_chan_t ),
        .ar_chan_t ( ar_chan_t ),
        .r_chan_t  (  r_chan_t ),
        .req_t     (     req_t ),
        .resp_t    (    resp_t )
      ) i_cut (
        .clk_i,
        .rst_ni,
        .slv_req_i  ( cut_req[i]    ),
        .slv_resp_o ( cut_resp[i]   ),
        .mst_req_o  ( cut_req[i+1]  ),
        .mst_resp_i ( cut_resp[i+1] )
      );
    end

    // connect master to the highest index
    assign mst_req_o        = cut_req[NoCuts];
    assign cut_resp[NoCuts] = mst_resp_i;
  end

  // Check the invariants
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert(NoCuts >= 0);
  end
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_multicut_intf #(
  parameter int unsigned ADDR_WIDTH = 0, // The address width.
  parameter int unsigned DATA_WIDTH = 0, // The data width.
  parameter int unsigned ID_WIDTH   = 0, // The ID width.
  parameter int unsigned USER_WIDTH = 0, // The user data width.
  parameter int unsigned NUM_CUTS   = 0  // The number of cuts.
) (
  input logic    clk_i,
  input logic    rst_ni,
  AXI_BUS.Slave  in,
  AXI_BUS.Master out
);

  typedef logic [ID_WIDTH-1:0]     id_t;
  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, in)
  `AXI_ASSIGN_FROM_RESP(in, slv_resp)

  `AXI_ASSIGN_FROM_REQ(out, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, out)

  axi_multicut #(
    .NoCuts    (  NUM_CUTS ),
    .aw_chan_t ( aw_chan_t ),
    .w_chan_t  (  w_chan_t ),
    .b_chan_t  (  b_chan_t ),
    .ar_chan_t ( ar_chan_t ),
    .r_chan_t  (  r_chan_t ),
    .req_t     (     req_t ),
    .resp_t    (    resp_t )
  ) i_axi_multicut (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

  // Check the invariants.
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (ADDR_WIDTH > 0) else $fatal(1, "Wrong addr width parameter");
    assert (DATA_WIDTH > 0) else $fatal(1, "Wrong data width parameter");
    assert (ID_WIDTH   > 0) else $fatal(1, "Wrong id   width parameter");
    assert (USER_WIDTH > 0) else $fatal(1, "Wrong user width parameter");
    assert (in.AXI_ADDR_WIDTH  == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (in.AXI_DATA_WIDTH  == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (in.AXI_ID_WIDTH    == ID_WIDTH)   else $fatal(1, "Wrong interface definition");
    assert (in.AXI_USER_WIDTH  == USER_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ID_WIDTH   == ID_WIDTH)   else $fatal(1, "Wrong interface definition");
    assert (out.AXI_USER_WIDTH == USER_WIDTH) else $fatal(1, "Wrong interface definition");
  end
  `endif
  // pragma translate_on
endmodule

module axi_lite_multicut_intf #(
  // The address width.
  parameter int unsigned ADDR_WIDTH = 0,
  // The data width.
  parameter int unsigned DATA_WIDTH = 0,
  // The number of cuts.
  parameter int unsigned NUM_CUTS   = 0
) (
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_LITE.Slave  in     ,
  AXI_LITE.Master out
);

  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;

  `AXI_LITE_ASSIGN_TO_REQ(slv_req, in)
  `AXI_LITE_ASSIGN_FROM_RESP(in, slv_resp)

  `AXI_LITE_ASSIGN_FROM_REQ(out, mst_req)
  `AXI_LITE_ASSIGN_TO_RESP(mst_resp, out)

  axi_multicut #(
    .NoCuts    (  NUM_CUTS ),
    .aw_chan_t ( aw_chan_t ),
    .w_chan_t  (  w_chan_t ),
    .b_chan_t  (  b_chan_t ),
    .ar_chan_t ( ar_chan_t ),
    .r_chan_t  (  r_chan_t ),
    .req_t     (     req_t ),
    .resp_t    (    resp_t )
  ) i_axi_multicut (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

  // Check the invariants.
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (ADDR_WIDTH > 0) else $fatal(1, "Wrong addr width parameter");
    assert (DATA_WIDTH > 0) else $fatal(1, "Wrong data width parameter");
    assert (in.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (in.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_ADDR_WIDTH == ADDR_WIDTH) else $fatal(1, "Wrong interface definition");
    assert (out.AXI_DATA_WIDTH == DATA_WIDTH) else $fatal(1, "Wrong interface definition");
  end
  `endif
  // pragma translate_on
endmodule
