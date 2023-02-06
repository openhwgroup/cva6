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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Luca Valente <luca.valente2@unibo.it>

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Destination-clock-domain half of the AXI CDC crossing.
///
/// For each of the five AXI channels, this module instantiates the source or destination half of
/// a CDC FIFO.  IMPORTANT: For each AXI channel, you MUST properly constrain three paths through
/// the FIFO; see the header of `cdc_fifo_gray` for instructions.
module axi_cdc_dst #(
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LogDepth = 1,
  parameter type aw_chan_t = logic,
  parameter type w_chan_t = logic,
  parameter type b_chan_t = logic,
  parameter type ar_chan_t = logic,
  parameter type r_chan_t = logic,
  parameter type axi_req_t = logic,
  parameter type axi_resp_t = logic
) (
  // asynchronous slave port
  input  aw_chan_t  [2**LogDepth-1:0] async_data_slave_aw_data_i,
  input  logic           [LogDepth:0] async_data_slave_aw_wptr_i,
  output logic           [LogDepth:0] async_data_slave_aw_rptr_o,
  input  w_chan_t   [2**LogDepth-1:0] async_data_slave_w_data_i,
  input  logic           [LogDepth:0] async_data_slave_w_wptr_i,
  output logic           [LogDepth:0] async_data_slave_w_rptr_o,
  output b_chan_t   [2**LogDepth-1:0] async_data_slave_b_data_o,
  output logic           [LogDepth:0] async_data_slave_b_wptr_o,
  input  logic           [LogDepth:0] async_data_slave_b_rptr_i,
  input  ar_chan_t  [2**LogDepth-1:0] async_data_slave_ar_data_i,
  input  logic           [LogDepth:0] async_data_slave_ar_wptr_i,
  output logic           [LogDepth:0] async_data_slave_ar_rptr_o,
  output r_chan_t   [2**LogDepth-1:0] async_data_slave_r_data_o,
  output logic           [LogDepth:0] async_data_slave_r_wptr_o,
  input  logic           [LogDepth:0] async_data_slave_r_rptr_i,
  // synchronous master port - clocked by `dst_clk_i`
  input  logic                        dst_clk_i,
  input  logic                        dst_rst_ni,
  output axi_req_t                    dst_req_o,
  input  axi_resp_t                   dst_resp_i
);

  cdc_fifo_gray_dst #(
    .T          ( logic [$bits(aw_chan_t)-1:0]  ),
    .LOG_DEPTH  ( LogDepth                      )
  ) i_cdc_fifo_gray_dst_aw (
    .async_data_i ( async_data_slave_aw_data_i  ),
    .async_wptr_i ( async_data_slave_aw_wptr_i  ),
    .async_rptr_o ( async_data_slave_aw_rptr_o  ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_data_o   ( dst_req_o.aw                ),
    .dst_valid_o  ( dst_req_o.aw_valid          ),
    .dst_ready_i  ( dst_resp_i.aw_ready         )
  );

  cdc_fifo_gray_dst #(
    .T          ( logic [$bits(w_chan_t)-1:0] ),
    .LOG_DEPTH  ( LogDepth                    )
  ) i_cdc_fifo_gray_dst_w (
    .async_data_i ( async_data_slave_w_data_i ),
    .async_wptr_i ( async_data_slave_w_wptr_i ),
    .async_rptr_o ( async_data_slave_w_rptr_o ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_data_o   ( dst_req_o.w               ),
    .dst_valid_o  ( dst_req_o.w_valid         ),
    .dst_ready_i  ( dst_resp_i.w_ready        )
  );

  cdc_fifo_gray_src #(
    .T          ( logic [$bits(b_chan_t)-1:0] ),
    .LOG_DEPTH  ( LogDepth                    )
  ) i_cdc_fifo_gray_src_b (
    .src_clk_i    ( dst_clk_i                 ),
    .src_rst_ni   ( dst_rst_ni                ),
    .src_data_i   ( dst_resp_i.b              ),
    .src_valid_i  ( dst_resp_i.b_valid        ),
    .src_ready_o  ( dst_req_o.b_ready         ),
    .async_data_o ( async_data_slave_b_data_o ),
    .async_wptr_o ( async_data_slave_b_wptr_o ),
    .async_rptr_i ( async_data_slave_b_rptr_i )
  );

  cdc_fifo_gray_dst #(
    .T          ( logic [$bits(ar_chan_t)-1:0]  ),
    .LOG_DEPTH  ( LogDepth                      )
  ) i_cdc_fifo_gray_dst_ar (
    .dst_clk_i,
    .dst_rst_ni,
    .dst_data_o   ( dst_req_o.ar                ),
    .dst_valid_o  ( dst_req_o.ar_valid          ),
    .dst_ready_i  ( dst_resp_i.ar_ready         ),
    .async_data_i ( async_data_slave_ar_data_i  ),
    .async_wptr_i ( async_data_slave_ar_wptr_i  ),
    .async_rptr_o ( async_data_slave_ar_rptr_o  )
  );

  cdc_fifo_gray_src #(
    .T          ( logic [$bits(r_chan_t)-1:0] ),
    .LOG_DEPTH  ( LogDepth                    )
  ) i_cdc_fifo_gray_src_r (
    .src_clk_i    ( dst_clk_i                 ),
    .src_rst_ni   ( dst_rst_ni                ),
    .src_data_i   ( dst_resp_i.r              ),
    .src_valid_i  ( dst_resp_i.r_valid        ),
    .src_ready_o  ( dst_req_o.r_ready         ),
    .async_data_o ( async_data_slave_r_data_o ),
    .async_wptr_o ( async_data_slave_r_wptr_o ),
    .async_rptr_i ( async_data_slave_r_rptr_i )
  );

endmodule


module axi_cdc_dst_intf #(
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1
) (
  // asynchronous slave port
  AXI_BUS_ASYNC_GRAY.Slave  src,
  // synchronous master port - clocked by `dst_clk_i`
  input  logic              dst_clk_i,
  input  logic              dst_rst_ni,
  AXI_BUS.Master            dst
);

  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t  dst_req;
  resp_t dst_resp;

  axi_cdc_dst #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( req_t     ),
    .axi_resp_t ( resp_t    ),
    .LogDepth   ( LOG_DEPTH )
  ) i_axi_cdc_dst (
    .async_data_slave_aw_data_i ( src.aw_data ),
    .async_data_slave_aw_wptr_i ( src.aw_wptr ),
    .async_data_slave_aw_rptr_o ( src.aw_rptr ),
    .async_data_slave_w_data_i  ( src.w_data  ),
    .async_data_slave_w_wptr_i  ( src.w_wptr  ),
    .async_data_slave_w_rptr_o  ( src.w_rptr  ),
    .async_data_slave_b_data_o  ( src.b_data  ),
    .async_data_slave_b_wptr_o  ( src.b_wptr  ),
    .async_data_slave_b_rptr_i  ( src.b_rptr  ),
    .async_data_slave_ar_data_i ( src.ar_data ),
    .async_data_slave_ar_wptr_i ( src.ar_wptr ),
    .async_data_slave_ar_rptr_o ( src.ar_rptr ),
    .async_data_slave_r_data_o  ( src.r_data  ),
    .async_data_slave_r_wptr_o  ( src.r_wptr  ),
    .async_data_slave_r_rptr_i  ( src.r_rptr  ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_req_o                  ( dst_req     ),
    .dst_resp_i                 ( dst_resp    )
  );

  `AXI_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_ASSIGN_TO_RESP(dst_resp, dst)

endmodule


module axi_lite_cdc_dst_intf #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  /// Depth of the FIFO crossing the clock domain, given as 2**LOG_DEPTH.
  parameter int unsigned LOG_DEPTH = 1
) (
  // asynchronous slave port
  AXI_LITE_ASYNC_GRAY.Slave   src,
  // synchronous master port - clocked by `dst_clk_i`
  input  logic                dst_clk_i,
  input  logic                dst_rst_ni,
  AXI_LITE.Master             dst
);

  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t   dst_req;
  resp_t  dst_resp;

  axi_cdc_dst #(
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .axi_req_t  ( req_t     ),
    .axi_resp_t ( resp_t    ),
    .LogDepth   ( LOG_DEPTH )
  ) i_axi_cdc_dst (
    .async_data_slave_aw_data_i ( src.aw_data ),
    .async_data_slave_aw_wptr_i ( src.aw_wptr ),
    .async_data_slave_aw_rptr_o ( src.aw_rptr ),
    .async_data_slave_w_data_i  ( src.w_data  ),
    .async_data_slave_w_wptr_i  ( src.w_wptr  ),
    .async_data_slave_w_rptr_o  ( src.w_rptr  ),
    .async_data_slave_b_data_o  ( src.b_data  ),
    .async_data_slave_b_wptr_o  ( src.b_wptr  ),
    .async_data_slave_b_rptr_i  ( src.b_rptr  ),
    .async_data_slave_ar_data_i ( src.ar_data ),
    .async_data_slave_ar_wptr_i ( src.ar_wptr ),
    .async_data_slave_ar_rptr_o ( src.ar_rptr ),
    .async_data_slave_r_data_o  ( src.r_data  ),
    .async_data_slave_r_wptr_o  ( src.r_wptr  ),
    .async_data_slave_r_rptr_i  ( src.r_rptr  ),
    .dst_clk_i,
    .dst_rst_ni,
    .dst_req_o                  ( dst_req     ),
    .dst_resp_i                 ( dst_resp    )
  );

  `AXI_LITE_ASSIGN_FROM_REQ(dst, dst_req)
  `AXI_LITE_ASSIGN_TO_RESP(dst_resp, dst)

endmodule
