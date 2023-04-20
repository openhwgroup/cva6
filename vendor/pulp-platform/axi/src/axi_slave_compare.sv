// Copyright (c) 2019-2020 ETH Zurich, University of Bologna
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
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "axi/assign.svh"
/// Synthesizable test module comparing two AXI slaves of the same type.
/// The reference response is always passed to the master, whereas the test response
/// is discarded after handshaking.
/// This module is meant to be used in FPGA-based verification.
module axi_slave_compare #(
    /// ID width of the AXI4+ATOP interface
    parameter int unsigned AxiIdWidth = 32'd0,
    /// FIFO depth
    parameter int unsigned FifoDepth  = 32'd0,
    /// AW channel type of the AXI4+ATOP interface
    parameter type axi_aw_chan_t = logic,
    /// W channel type of the AXI4+ATOP interface
    parameter type axi_w_chan_t  = logic,
    /// B channel type of the AXI4+ATOP interface
    parameter type axi_b_chan_t  = logic,
    /// AR channel type of the AXI4+ATOP interface
    parameter type axi_ar_chan_t = logic,
    /// R channel type of the AXI4+ATOP interface
    parameter type axi_r_chan_t  = logic,
    /// Request struct type of the AXI4+ATOP slave port
    parameter type axi_req_t     = logic,
    /// Response struct type of the AXI4+ATOP slave port
    parameter type axi_rsp_t     = logic,
    /// ID type (*do not overwrite*)
    parameter type id_t          = logic [2**AxiIdWidth-1:0]
)(
    /// Clock
    input  logic     clk_i,
    /// Asynchronous reset, active low
    input  logic     rst_ni,
    /// Testmode
    input  logic     testmode_i,
    /// AXI4+ATOP channel request in
    input  axi_req_t axi_mst_req_i,
    /// AXI4+ATOP channel response out
    output axi_rsp_t axi_mst_rsp_o,
    /// AXI4+ATOP reference channel request out
    output axi_req_t axi_ref_req_o,
    /// AXI4+ATOP reference channel response in
    input  axi_rsp_t axi_ref_rsp_i,
    /// AXI4+ATOP test channel request out
    output axi_req_t axi_test_req_o,
    /// AXI4+ATOP test channel response in
    input  axi_rsp_t axi_test_rsp_i,
    /// AW mismatch
    output id_t      aw_mismatch_o,
    /// W mismatch
    output logic     w_mismatch_o,
    /// B mismatch
    output id_t      b_mismatch_o,
    /// AR mismatch
    output id_t      ar_mismatch_o,
    /// R mismatch
    output id_t      r_mismatch_o,
    /// General mismatch
    output logic     mismatch_o,
    /// Unit is busy
    output logic     busy_o
);

    axi_req_t axi_ref_req_in, axi_test_req_in;
    axi_rsp_t axi_ref_rsp_in, axi_test_rsp_in;

    logic aw_valid_ref, aw_ready_ref;
    logic w_valid_ref,  w_ready_ref;
    logic ar_valid_ref, ar_ready_ref;

    logic aw_valid_test, aw_ready_test;
    logic w_valid_test,  w_ready_test;
    logic ar_valid_test, ar_ready_test;

    logic aw_ready_mst;
    logic w_ready_mst;
    logic ar_ready_mst;

    stream_fork #(
        .N_OUP   ( 32'd2  )
    ) i_stream_fork_aw (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_mst_req_i.aw_valid          ),
        .ready_o ( aw_ready_mst                    ),
        .valid_o ( { aw_valid_ref, aw_valid_test } ),
        .ready_i ( { aw_ready_ref, aw_ready_test } )
    );

    stream_fork #(
        .N_OUP   ( 32'd2  )
      ) i_stream_fork_ar (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_mst_req_i.ar_valid          ),
        .ready_o ( ar_ready_mst                    ),
        .valid_o ( { ar_valid_ref, ar_valid_test } ),
        .ready_i ( { ar_ready_ref, ar_ready_test } )
    );

    stream_fork #(
        .N_OUP   ( 32'd2  )
    ) i_stream_fork_w (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_mst_req_i.w_valid         ),
        .ready_o ( w_ready_mst                   ),
        .valid_o ( { w_valid_ref, w_valid_test } ),
        .ready_i ( { w_ready_ref, w_ready_test } )
    );

  // assemble buses
  always_comb begin
    // request
    `AXI_SET_REQ_STRUCT(axi_ref_req_in, axi_mst_req_i)
    `AXI_SET_REQ_STRUCT(axi_test_req_in, axi_mst_req_i)
    // overwrite valids in requests
    axi_ref_req_in.aw_valid  = aw_valid_ref;
    axi_ref_req_in.ar_valid  = ar_valid_ref;
    axi_ref_req_in.w_valid   = w_valid_ref;
    axi_test_req_in.aw_valid = aw_valid_test;
    axi_test_req_in.ar_valid = ar_valid_test;
    axi_test_req_in.w_valid  = w_valid_test;
    // get readies
    aw_ready_ref  = axi_ref_rsp_in.aw_ready;
    ar_ready_ref  = axi_ref_rsp_in.ar_ready;
    w_ready_ref   = axi_ref_rsp_in.w_ready;
    aw_ready_test = axi_test_rsp_in.aw_ready;
    ar_ready_test = axi_test_rsp_in.ar_ready;
    w_ready_test  = axi_test_rsp_in.w_ready;
    // response
    `AXI_SET_RESP_STRUCT(axi_mst_rsp_o, axi_ref_rsp_in)
    // overwrite readies
    axi_mst_rsp_o.aw_ready  = aw_ready_mst;
    axi_mst_rsp_o.w_ready   = w_ready_mst;
    axi_mst_rsp_o.ar_ready  = ar_ready_mst;
    // b interface is not used
    axi_test_req_in.r_ready = '1;
    axi_test_req_in.b_ready = '1;
  end

  axi_bus_compare #(
    .AxiIdWidth     ( AxiIdWidth      ),
    .FifoDepth      ( FifoDepth       ),
    .axi_aw_chan_t  ( axi_aw_chan_t   ),
    .axi_w_chan_t   ( axi_w_chan_t    ),
    .axi_b_chan_t   ( axi_b_chan_t    ),
    .axi_ar_chan_t  ( axi_ar_chan_t   ),
    .axi_r_chan_t   ( axi_r_chan_t    ),
    .axi_req_t      ( axi_req_t       ),
    .axi_rsp_t      ( axi_rsp_t       )
  ) i_axi_bus_compare (
    .clk_i,
    .rst_ni,
    .testmode_i,
    .aw_mismatch_o,
    .w_mismatch_o,
    .b_mismatch_o,
    .ar_mismatch_o,
    .r_mismatch_o,
    .mismatch_o,
    .busy_o,
    .axi_a_req_i   ( axi_ref_req_in   ),
    .axi_a_rsp_o   ( axi_ref_rsp_in   ),
    .axi_a_req_o   ( axi_ref_req_o    ),
    .axi_a_rsp_i   ( axi_ref_rsp_i    ),
    .axi_b_req_i   ( axi_test_req_in  ),
    .axi_b_rsp_o   ( axi_test_rsp_in  ),
    .axi_b_req_o   ( axi_test_req_o   ),
    .axi_b_rsp_i   ( axi_test_rsp_i   )
  );

endmodule
