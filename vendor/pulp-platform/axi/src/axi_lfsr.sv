// Copyright 2022 ETH Zurich and University of Bologna.
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

`include "axi/typedef.svh"

/// AXI4 LFSR Subordinate device. Responds with a pseudo random answer. Serial interface to
/// set the internal state.
module axi_lfsr #(
    /// AXI4 Data Width
    parameter int unsigned DataWidth = 32'd0,
    /// AXI4 Addr Width
    parameter int unsigned AddrWidth = 32'd0,
    /// AXI4 Id Width
    parameter int unsigned IdWidth   = 32'd0,
    /// AXI4 User Width
    parameter int unsigned UserWidth = 32'd0,
    /// AXI4 request struct definition
    parameter type axi_req_t         = logic,
    /// AXI4 response struct definition
    parameter type axi_rsp_t         = logic
)(
    /// Rising-edge clock
    input  logic     clk_i,
    /// Active-low reset
    input  logic     rst_ni,
    /// Testmode
    input  logic     testmode_i,
    /// AXI4 request struct
    input  axi_req_t req_i,
    /// AXI4 response struct
    output axi_rsp_t rsp_o,
    /// Serial shift data in (write)
    input  logic     w_ser_data_i,
    /// Serial shift data out (write)
    output logic     w_ser_data_o,
    /// Serial shift enable (write)
    input  logic     w_ser_en_i,
    /// Serial shift data in (read)
    input  logic     r_ser_data_i,
    /// Serial shift data out (read)
    output logic     r_ser_data_o,
    /// Serial shift enable (read)
    input  logic     r_ser_en_i
);

    /// AXI4 Strobe Width
    localparam int unsigned StrbWidth = DataWidth / 8;

    /// Address Type
    typedef logic [AddrWidth-1:0] addr_t;
    /// Data type
    typedef logic [DataWidth-1:0] data_t;
    /// Strobe Type
    typedef logic [StrbWidth-1:0] strb_t;

    // AXI Lite typedef
    `AXI_LITE_TYPEDEF_AW_CHAN_T(axi_lite_aw_chan_t, addr_t)
    `AXI_LITE_TYPEDEF_W_CHAN_T(axi_lite_w_chan_t, data_t, strb_t)
    `AXI_LITE_TYPEDEF_B_CHAN_T(axi_lite_b_chan_t)

    `AXI_LITE_TYPEDEF_AR_CHAN_T(axi_lite_ar_chan_t, addr_t)
    `AXI_LITE_TYPEDEF_R_CHAN_T(axi_lite_r_chan_t, data_t)

    `AXI_LITE_TYPEDEF_REQ_T(axi_lite_req_t, axi_lite_aw_chan_t, axi_lite_w_chan_t, axi_lite_ar_chan_t)
    `AXI_LITE_TYPEDEF_RESP_T(axi_lite_rsp_t, axi_lite_b_chan_t, axi_lite_r_chan_t)

    // AXI Lite buses
    axi_lite_req_t axi_lite_req;
    axi_lite_rsp_t axi_lite_rsp;

    axi_to_axi_lite #(
        .AxiAddrWidth    ( AddrWidth      ),
        .AxiDataWidth    ( DataWidth      ),
        .AxiIdWidth      ( IdWidth        ),
        .AxiUserWidth    ( UserWidth      ),
        .AxiMaxWriteTxns ( 'd2            ), // We only have 1 cycle latency; 2 is enough
        .AxiMaxReadTxns  ( 'd2            ), // We only have 1 cycle latency; 2 is enough
        .FallThrough     ( 1'b0           ),
        .full_req_t      ( axi_req_t      ),
        .full_resp_t     ( axi_rsp_t      ),
        .lite_req_t      ( axi_lite_req_t ),
        .lite_resp_t     ( axi_lite_rsp_t )
    ) i_axi_to_axi_lite (
        .clk_i,
        .rst_ni,
        .test_i     ( testmode_i   ),
        .slv_req_i  ( req_i        ),
        .slv_resp_o ( rsp_o        ),
        .mst_req_o  ( axi_lite_req ),
        .mst_resp_i ( axi_lite_rsp )
    );

    axi_lite_lfsr #(
        .DataWidth      ( DataWidth      ),
        .axi_lite_req_t ( axi_lite_req_t ),
        .axi_lite_rsp_t ( axi_lite_rsp_t )
    ) i_axi_lite_lfsr (
        .clk_i,
        .rst_ni,
        .testmode_i,
        .w_ser_data_i,
        .w_ser_data_o,
        .w_ser_en_i,
        .r_ser_data_i,
        .r_ser_data_o,
        .r_ser_en_i,
        .req_i        ( axi_lite_req ),
        .rsp_o        ( axi_lite_rsp )
    );

endmodule : axi_lfsr
