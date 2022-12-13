// Copyright 2020 ETH Zurich and University of Bologna.
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
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

// NOTE: The upsizer does not support WRAP bursts, and will answer with SLVERR
// upon receiving a burst of such type. In addition to that, the downsizer also
// does not support FIXED bursts with incoming axlen != 0.

module axi_dw_converter #(
    parameter int unsigned AxiMaxReads         = 1    , // Number of outstanding reads
    parameter int unsigned AxiSlvPortDataWidth = 8    , // Data width of the slv port
    parameter int unsigned AxiMstPortDataWidth = 8    , // Data width of the mst port
    parameter int unsigned AxiAddrWidth        = 1    , // Address width
    parameter int unsigned AxiIdWidth          = 1    , // ID width
    parameter type aw_chan_t                   = logic, // AW Channel Type
    parameter type mst_w_chan_t                = logic, //  W Channel Type for the mst port
    parameter type slv_w_chan_t                = logic, //  W Channel Type for the slv port
    parameter type b_chan_t                    = logic, //  B Channel Type
    parameter type ar_chan_t                   = logic, // AR Channel Type
    parameter type mst_r_chan_t                = logic, //  R Channel Type for the mst port
    parameter type slv_r_chan_t                = logic, //  R Channel Type for the slv port
    parameter type axi_mst_req_t               = logic, // AXI Request Type for mst ports
    parameter type axi_mst_resp_t              = logic, // AXI Response Type for mst ports
    parameter type axi_slv_req_t               = logic, // AXI Request Type for slv ports
    parameter type axi_slv_resp_t              = logic  // AXI Response Type for slv ports
  ) (
    input  logic          clk_i,
    input  logic          rst_ni,
    // Slave interface
    input  axi_slv_req_t  slv_req_i,
    output axi_slv_resp_t slv_resp_o,
    // Master interface
    output axi_mst_req_t  mst_req_o,
    input  axi_mst_resp_t mst_resp_i
  );

  if (AxiMstPortDataWidth == AxiSlvPortDataWidth) begin: gen_no_dw_conversion
    assign mst_req_o  = slv_req_i ;
    assign slv_resp_o = mst_resp_i;
  end : gen_no_dw_conversion

  if (AxiMstPortDataWidth > AxiSlvPortDataWidth) begin: gen_dw_upsize
    axi_dw_upsizer #(
      .AxiMaxReads        (AxiMaxReads        ),
      .AxiSlvPortDataWidth(AxiSlvPortDataWidth),
      .AxiMstPortDataWidth(AxiMstPortDataWidth),
      .AxiAddrWidth       (AxiAddrWidth       ),
      .AxiIdWidth         (AxiIdWidth         ),
      .aw_chan_t          (aw_chan_t          ),
      .mst_w_chan_t       (mst_w_chan_t       ),
      .slv_w_chan_t       (slv_w_chan_t       ),
      .b_chan_t           (b_chan_t           ),
      .ar_chan_t          (ar_chan_t          ),
      .mst_r_chan_t       (mst_r_chan_t       ),
      .slv_r_chan_t       (slv_r_chan_t       ),
      .axi_mst_req_t      (axi_mst_req_t      ),
      .axi_mst_resp_t     (axi_mst_resp_t     ),
      .axi_slv_req_t      (axi_slv_req_t      ),
      .axi_slv_resp_t     (axi_slv_resp_t     )
    ) i_axi_dw_upsizer (
      .clk_i     (clk_i     ),
      .rst_ni    (rst_ni    ),
      // Slave interface
      .slv_req_i (slv_req_i ),
      .slv_resp_o(slv_resp_o),
      // Master interface
      .mst_req_o (mst_req_o ),
      .mst_resp_i(mst_resp_i)
    );
  end : gen_dw_upsize

  if (AxiMstPortDataWidth < AxiSlvPortDataWidth) begin: gen_dw_downsize
    axi_dw_downsizer #(
      .AxiMaxReads        (AxiMaxReads        ),
      .AxiSlvPortDataWidth(AxiSlvPortDataWidth),
      .AxiMstPortDataWidth(AxiMstPortDataWidth),
      .AxiAddrWidth       (AxiAddrWidth       ),
      .AxiIdWidth         (AxiIdWidth         ),
      .aw_chan_t          (aw_chan_t          ),
      .mst_w_chan_t       (mst_w_chan_t       ),
      .slv_w_chan_t       (slv_w_chan_t       ),
      .b_chan_t           (b_chan_t           ),
      .ar_chan_t          (ar_chan_t          ),
      .mst_r_chan_t       (mst_r_chan_t       ),
      .slv_r_chan_t       (slv_r_chan_t       ),
      .axi_mst_req_t      (axi_mst_req_t      ),
      .axi_mst_resp_t     (axi_mst_resp_t     ),
      .axi_slv_req_t      (axi_slv_req_t      ),
      .axi_slv_resp_t     (axi_slv_resp_t     )
    ) i_axi_dw_downsizer (
      .clk_i     (clk_i     ),
      .rst_ni    (rst_ni    ),
      // Slave interface
      .slv_req_i (slv_req_i ),
      .slv_resp_o(slv_resp_o),
      // Master interface
      .mst_req_o (mst_req_o ),
      .mst_resp_i(mst_resp_i)
    );
  end : gen_dw_downsize

endmodule : axi_dw_converter

// Interface wrapper

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_dw_converter_intf #(
    parameter int unsigned AXI_ID_WIDTH            = 1,
    parameter int unsigned AXI_ADDR_WIDTH          = 1,
    parameter int unsigned AXI_SLV_PORT_DATA_WIDTH = 8,
    parameter int unsigned AXI_MST_PORT_DATA_WIDTH = 8,
    parameter int unsigned AXI_USER_WIDTH          = 0,
    parameter int unsigned AXI_MAX_READS           = 8
  ) (
    input          logic clk_i,
    input          logic rst_ni,
    AXI_BUS.Slave        slv,
    AXI_BUS.Master       mst
  );

  typedef logic [AXI_ID_WIDTH-1:0] id_t                   ;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t               ;
  typedef logic [AXI_MST_PORT_DATA_WIDTH-1:0] mst_data_t  ;
  typedef logic [AXI_MST_PORT_DATA_WIDTH/8-1:0] mst_strb_t;
  typedef logic [AXI_SLV_PORT_DATA_WIDTH-1:0] slv_data_t  ;
  typedef logic [AXI_SLV_PORT_DATA_WIDTH/8-1:0] slv_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t               ;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, mst_data_t, mst_strb_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, slv_data_t, slv_strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, mst_data_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, slv_data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, aw_chan_t, mst_w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, b_chan_t, mst_r_chan_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, aw_chan_t, slv_w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, b_chan_t, slv_r_chan_t)

  slv_req_t  slv_req;
  slv_resp_t slv_resp;
  mst_req_t  mst_req;
  mst_resp_t mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_dw_converter #(
    .AxiMaxReads        ( AXI_MAX_READS           ),
    .AxiSlvPortDataWidth( AXI_SLV_PORT_DATA_WIDTH ),
    .AxiMstPortDataWidth( AXI_MST_PORT_DATA_WIDTH ),
    .AxiAddrWidth       ( AXI_ADDR_WIDTH          ),
    .AxiIdWidth         ( AXI_ID_WIDTH            ),
    .aw_chan_t          ( aw_chan_t               ),
    .mst_w_chan_t       ( mst_w_chan_t            ),
    .slv_w_chan_t       ( slv_w_chan_t            ),
    .b_chan_t           ( b_chan_t                ),
    .ar_chan_t          ( ar_chan_t               ),
    .mst_r_chan_t       ( mst_r_chan_t            ),
    .slv_r_chan_t       ( slv_r_chan_t            ),
    .axi_mst_req_t      ( mst_req_t               ),
    .axi_mst_resp_t     ( mst_resp_t              ),
    .axi_slv_req_t      ( slv_req_t               ),
    .axi_slv_resp_t     ( slv_resp_t              )
  ) i_axi_dw_converter (
    .clk_i      ( clk_i    ),
    .rst_ni     ( rst_ni   ),
    // slave port
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    // master port
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

endmodule : axi_dw_converter_intf
