// Copyright (c) 20192-2020 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Andreas Kurth <akurth@iis.ee.ethz.ch>
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "axi/assign.svh"

/// A clock domain crossing on an AXI interface.
///
/// For each of the five AXI channels, this module instantiates a CDC FIFO, whose push and pop
/// ports are in separate clock domains.  IMPORTANT: For each AXI channel, you MUST properly
/// constrain three paths through the FIFO; see the header of `cdc_fifo_gray` for instructions.
module axi_cdc #(
  parameter type aw_chan_t  = logic, // AW Channel Type
  parameter type w_chan_t   = logic, //  W Channel Type
  parameter type b_chan_t   = logic, //  B Channel Type
  parameter type ar_chan_t  = logic, // AR Channel Type
  parameter type r_chan_t   = logic, //  R Channel Type
  parameter type axi_req_t  = logic, // encapsulates request channels
  parameter type axi_resp_t = logic, // encapsulates request channels
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned  LogDepth  = 1
) (
  // slave side - clocked by `src_clk_i`
  input  logic      src_clk_i,
  input  logic      src_rst_ni,
  input  axi_req_t  src_req_i,
  output axi_resp_t src_resp_o,
  // master side - clocked by `dst_clk_i`
  input  logic      dst_clk_i,
  input  logic      dst_rst_ni,
  output axi_req_t  dst_req_o,
  input  axi_resp_t dst_resp_i
);

    cdc_fifo_gray #(
        //  We need to cast to bits here because of some arbitrary bug in Synopsys.
        .WIDTH       ( $bits(aw_chan_t)    ),
        .LOG_DEPTH   ( LogDepth            )
    ) i_cdc_fifo_gray_aw (
        .src_rst_ni,
        .src_clk_i,
        .src_data_i  ( src_req_i.aw        ),
        .src_valid_i ( src_req_i.aw_valid  ),
        .src_ready_o ( src_resp_o.aw_ready ),
        .dst_rst_ni,
        .dst_clk_i,
        .dst_data_o  ( dst_req_o.aw        ),
        .dst_valid_o ( dst_req_o.aw_valid  ),
        .dst_ready_i ( dst_resp_i.aw_ready )
    );

    cdc_fifo_gray #(
        .WIDTH       ( $bits(w_chan_t)    ),
        .LOG_DEPTH   ( LogDepth           )
    ) i_cdc_fifo_gray_w (
        .src_rst_ni,
        .src_clk_i,
        .src_data_i  ( src_req_i.w        ),
        .src_valid_i ( src_req_i.w_valid  ),
        .src_ready_o ( src_resp_o.w_ready ),
        .dst_rst_ni,
        .dst_clk_i,
        .dst_data_o  ( dst_req_o.w        ),
        .dst_valid_o ( dst_req_o.w_valid  ),
        .dst_ready_i ( dst_resp_i.w_ready )
    );

    cdc_fifo_gray #(
        .WIDTH       ( $bits(b_chan_t)    ),
        .LOG_DEPTH   ( LogDepth           )
    ) i_cdc_fifo_gray_b (
        .src_rst_ni  ( dst_rst_ni         ),
        .src_clk_i   ( dst_clk_i          ),
        .src_data_i  ( dst_resp_i.b       ),
        .src_valid_i ( dst_resp_i.b_valid ),
        .src_ready_o ( dst_req_o.b_ready  ),
        .dst_rst_ni  ( src_rst_ni         ),
        .dst_clk_i   ( src_clk_i          ),
        .dst_data_o  ( src_resp_o.b       ),
        .dst_valid_o ( src_resp_o.b_valid ),
        .dst_ready_i ( src_req_i.b_ready  )
    );

    cdc_fifo_gray #(
        .WIDTH       ( $bits(ar_chan_t)    ),
        .LOG_DEPTH   ( LogDepth            )
    ) i_cdc_fifo_gray_ar (
        .src_rst_ni,
        .src_clk_i,
        .src_data_i  ( src_req_i.ar        ),
        .src_valid_i ( src_req_i.ar_valid  ),
        .src_ready_o ( src_resp_o.ar_ready ),
        .dst_rst_ni,
        .dst_clk_i,
        .dst_data_o  ( dst_req_o.ar        ),
        .dst_valid_o ( dst_req_o.ar_valid  ),
        .dst_ready_i ( dst_resp_i.ar_ready )
    );

    cdc_fifo_gray #(
        .WIDTH       ( $bits(r_chan_t)    ),
        .LOG_DEPTH   ( LogDepth           )
    ) i_cdc_fifo_gray_r (
        .src_rst_ni  ( dst_rst_ni         ),
        .src_clk_i   ( dst_clk_i          ),
        .src_data_i  ( dst_resp_i.r       ),
        .src_valid_i ( dst_resp_i.r_valid ),
        .src_ready_o ( dst_req_o.r_ready  ),
        .dst_rst_ni  ( src_rst_ni         ),
        .dst_clk_i   ( src_clk_i          ),
        .dst_data_o  ( src_resp_o.r       ),
        .dst_valid_o ( src_resp_o.r_valid ),
        .dst_ready_i ( src_req_i.r_ready  )
    );

endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

// interface wrapper
module axi_cdc_intf #(
  parameter int unsigned AXI_ID_WIDTH   = 0,
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1
) (
   // slave side - clocked by `src_clk_i`
  input  logic      src_clk_i,
  input  logic      src_rst_ni,
  AXI_BUS.Slave     src,
  // master side - clocked by `dst_clk_i`
  input  logic      dst_clk_i,
  input  logic      dst_rst_ni,
  AXI_BUS.Master    dst
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T ( aw_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_W_CHAN_T  (  w_chan_t, data_t,       strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T  (  b_chan_t,         id_t,         user_t);
  `AXI_TYPEDEF_AR_CHAN_T ( ar_chan_t, addr_t, id_t,         user_t);
  `AXI_TYPEDEF_R_CHAN_T  (  r_chan_t, data_t, id_t,         user_t);
  `AXI_TYPEDEF_REQ_T     (     req_t, aw_chan_t, w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T    (    resp_t,  b_chan_t, r_chan_t);

  req_t  src_req,  dst_req;
  resp_t src_resp, dst_resp;

  `AXI_ASSIGN_TO_REQ    ( src_req,  src      );
  `AXI_ASSIGN_FROM_RESP ( src,      src_resp );

  `AXI_ASSIGN_FROM_REQ  ( dst     , dst_req  );
  `AXI_ASSIGN_TO_RESP   ( dst_resp, dst      );

  axi_cdc #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( req_t     ),
    .axi_resp_t ( resp_t    ),
    .LogDepth   ( LOG_DEPTH )
  ) i_axi_cdc (
    .src_clk_i,
    .src_rst_ni,
    .src_req_i  ( src_req  ),
    .src_resp_o ( src_resp ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_req_o  ( dst_req  ),
    .dst_resp_i ( dst_resp )
  );

  endmodule
