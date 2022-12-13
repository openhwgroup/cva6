// Copyright (c) 2020 ETH Zurich, University of Bologna
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
// - Andreas Kurth       <akurth@iis.ee.ethz.ch>

`include "axi/assign.svh"
`include "axi/typedef.svh"

/// Reduce AXI IDs by serializing transactions when necessary.
///
/// This module is designed to remap a wide ID space to an arbitrarily narrow ID space.  If
/// necessary, this module maps two different IDs at its slave port to the same ID at its master
/// port, thereby constraining the order of those transactions and in this sense *serializing* them.
/// If the independence of IDs needs to be retained at the cost of a wider ID space at the master
/// port, use [`axi_id_remap`](module.axi_id_remap) instead.
///
/// This module contains one [`axi_serializer`](module.axi_serializer) per master port ID (given by
/// the `AxiMstPortMaxUniqIds parameter`).
module axi_id_serialize #(
  /// ID width of the AXI4+ATOP slave port
  parameter int unsigned AxiSlvPortIdWidth = 32'd0,
  /// Maximum number of transactions that can be in flight at the slave port.  Reads and writes are
  /// counted separately (except for ATOPs, which count as both read and write).
  parameter int unsigned AxiSlvPortMaxTxns = 32'd0,
  /// ID width of the AXI4+ATOP master port
  parameter int unsigned AxiMstPortIdWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at the master port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// The maximum value of this parameter is `2**AxiMstPortIdWidth`.
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the master port.
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd0,
  /// Address width of both AXI4+ATOP ports
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// Data width of both AXI4+ATOP ports
  parameter int unsigned AxiDataWidth = 32'd0,
  /// User width of both AXI4+ATOP ports
  parameter int unsigned AxiUserWidth = 32'd0,
  /// Request struct type of the AXI4+ATOP slave port
  parameter type slv_req_t = logic,
  /// Response struct type of the AXI4+ATOP slave port
  parameter type slv_resp_t = logic,
  /// Request struct type of the AXI4+ATOP master port
  parameter type mst_req_t = logic,
  /// Response struct type of the AXI4+ATOP master port
  parameter type mst_resp_t = logic
) (
  /// Rising-edge clock of both ports
  input  logic      clk_i,
  /// Asynchronous reset, active low
  input  logic      rst_ni,
  /// Slave port request
  input  slv_req_t  slv_req_i,
  /// Slave port response
  output slv_resp_t slv_resp_o,
  /// Master port request
  output mst_req_t  mst_req_o,
  /// Master port response
  input  mst_resp_t mst_resp_i
);

  /// Number of bits of the slave port ID that determine the mapping to the master port ID
  localparam int unsigned SelectWidth = cf_math_pkg::idx_width(AxiMstPortMaxUniqIds);
  /// Slice of slave port IDs that determines the master port ID
  typedef logic [SelectWidth-1:0] select_t;

  /// ID width after the multiplexer
  localparam int unsigned MuxIdWidth = (AxiMstPortMaxUniqIds > 32'd1) ? SelectWidth + 32'd1 : 32'd1;

  /// ID after serializer (i.e., with a constant value of zero)
  typedef logic [0:0]                   ser_id_t;
  /// ID after the multiplexer
  typedef logic [MuxIdWidth-1:0]        mux_id_t;
  /// ID at the slave port
  typedef logic [AxiSlvPortIdWidth-1:0] slv_id_t;
  /// ID at the master port
  typedef logic [AxiMstPortIdWidth-1:0] mst_id_t;
  /// Address in any AXI channel
  typedef logic [AxiAddrWidth-1:0]      addr_t;
  /// Data in any AXI channel
  typedef logic [AxiDataWidth-1:0]      data_t;
  /// Strobe in any AXI channel
  typedef logic [AxiDataWidth/8-1:0]    strb_t;
  /// User signal in any AXI channel
  typedef logic [AxiUserWidth-1:0]      user_t;

  /// W channel at any interface
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)

  /// AW channel at slave port
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_t, addr_t, slv_id_t, user_t)
  /// B channel at slave port
  `AXI_TYPEDEF_B_CHAN_T(slv_b_t, slv_id_t, user_t)
  /// AR channel at slave port
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_t, addr_t, slv_id_t, user_t)
  /// R channel at slave port
  `AXI_TYPEDEF_R_CHAN_T(slv_r_t, data_t, slv_id_t, user_t)

  /// AW channel after serializer
  `AXI_TYPEDEF_AW_CHAN_T(ser_aw_t, addr_t, ser_id_t, user_t)
  /// B channel after serializer
  `AXI_TYPEDEF_B_CHAN_T(ser_b_t, ser_id_t, user_t)
  /// AR channel after serializer
  `AXI_TYPEDEF_AR_CHAN_T(ser_ar_t, addr_t, ser_id_t, user_t)
  /// R channel after serializer
  `AXI_TYPEDEF_R_CHAN_T(ser_r_t, data_t, ser_id_t, user_t)
  /// AXI Requests from serializer
  `AXI_TYPEDEF_REQ_T(ser_req_t, ser_aw_t, w_t, ser_ar_t)
  /// AXI responses to serializer
  `AXI_TYPEDEF_RESP_T(ser_resp_t, ser_b_t, ser_r_t)

  /// AW channel after the multiplexer
  `AXI_TYPEDEF_AW_CHAN_T(mux_aw_t, addr_t, mux_id_t, user_t)
  /// B channel after the multiplexer
  `AXI_TYPEDEF_B_CHAN_T(mux_b_t, mux_id_t, user_t)
  /// AR channel after the multiplexer
  `AXI_TYPEDEF_AR_CHAN_T(mux_ar_t, addr_t, mux_id_t, user_t)
  /// R channel after the multiplexer
  `AXI_TYPEDEF_R_CHAN_T(mux_r_t, data_t, mux_id_t, user_t)
  /// AXI requests from the multiplexer
  `AXI_TYPEDEF_REQ_T(mux_req_t, mux_aw_t, w_t, mux_ar_t)
  /// AXI responses to the multiplexer
  `AXI_TYPEDEF_RESP_T(mux_resp_t, mux_b_t, mux_r_t)

  /// AW channel at master port
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_t, addr_t, mst_id_t, user_t)
  /// B channel at master port
  `AXI_TYPEDEF_B_CHAN_T(mst_b_t, mst_id_t, user_t)
  /// AR channel at master port
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_t, addr_t, mst_id_t, user_t)
  /// R channel at master port
  `AXI_TYPEDEF_R_CHAN_T(mst_r_t, data_t, mst_id_t, user_t)

  select_t slv_aw_select, slv_ar_select;
  assign slv_aw_select = select_t'(slv_req_i.aw.id % AxiMstPortMaxUniqIds); // TODO: customizable base
  assign slv_ar_select = select_t'(slv_req_i.ar.id % AxiMstPortMaxUniqIds);

  slv_req_t  [AxiMstPortMaxUniqIds-1:0] to_serializer_reqs;
  slv_resp_t [AxiMstPortMaxUniqIds-1:0] to_serializer_resps;

  axi_demux #(
    .AxiIdWidth  ( AxiSlvPortIdWidth    ),
    .aw_chan_t   ( slv_aw_t             ),
    .w_chan_t    ( w_t                  ),
    .b_chan_t    ( slv_b_t              ),
    .ar_chan_t   ( slv_ar_t             ),
    .r_chan_t    ( slv_r_t              ),
    .req_t       ( slv_req_t            ),
    .resp_t      ( slv_resp_t           ),
    .NoMstPorts  ( AxiMstPortMaxUniqIds ),
    .MaxTrans    ( AxiSlvPortMaxTxns    ),
    .AxiLookBits ( AxiSlvPortIdWidth    ),
    .FallThrough ( 1'b1                 ),
    .SpillAw     ( 1'b1                 ),
    .SpillW      ( 1'b0                 ),
    .SpillB      ( 1'b0                 ),
    .SpillAr     ( 1'b1                 ),
    .SpillR      ( 1'b0                 )
  ) i_axi_demux (
    .clk_i,
    .rst_ni,
    .test_i          ( 1'b0                ),
    .slv_req_i       ( slv_req_i           ),
    .slv_aw_select_i ( slv_aw_select       ),
    .slv_ar_select_i ( slv_ar_select       ),
    .slv_resp_o      ( slv_resp_o          ),
    .mst_reqs_o      ( to_serializer_reqs  ),
    .mst_resps_i     ( to_serializer_resps )
  );

  slv_req_t  [AxiMstPortMaxUniqIds-1:0] tmp_serializer_reqs;
  slv_resp_t [AxiMstPortMaxUniqIds-1:0] tmp_serializer_resps;
  ser_req_t  [AxiMstPortMaxUniqIds-1:0] from_serializer_reqs;
  ser_resp_t [AxiMstPortMaxUniqIds-1:0] from_serializer_resps;

  for (genvar i = 0; i < AxiMstPortMaxUniqIds; i++) begin : gen_serializers
    axi_serializer #(
      .MaxReadTxns  ( AxiMstPortMaxTxnsPerId  ),
      .MaxWriteTxns ( AxiMstPortMaxTxnsPerId  ),
      .AxiIdWidth   ( AxiSlvPortIdWidth       ),
      .req_t        ( slv_req_t               ),
      .resp_t       ( slv_resp_t              )
    ) i_axi_serializer (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( to_serializer_reqs[i]   ),
      .slv_resp_o ( to_serializer_resps[i]  ),
      .mst_req_o  ( tmp_serializer_reqs[i]  ),
      .mst_resp_i ( tmp_serializer_resps[i] )
    );
    always_comb begin
      `AXI_SET_REQ_STRUCT(from_serializer_reqs[i], tmp_serializer_reqs[i])
      // Truncate to ID width 1 as all requests have ID '0.
      from_serializer_reqs[i].aw.id = tmp_serializer_reqs[i].aw.id[0];
      from_serializer_reqs[i].ar.id = tmp_serializer_reqs[i].ar.id[0];
      `AXI_SET_RESP_STRUCT(tmp_serializer_resps[i], from_serializer_resps[i])
      // Zero-extend response IDs.
      tmp_serializer_resps[i].b.id = {{AxiSlvPortIdWidth-1{1'b0}}, from_serializer_resps[i].b.id};
      tmp_serializer_resps[i].r.id = {{AxiSlvPortIdWidth-1{1'b0}}, from_serializer_resps[i].r.id};
    end
  end

  mux_req_t  axi_mux_req;
  mux_resp_t axi_mux_resp;

  axi_mux #(
    .SlvAxiIDWidth ( 32'd1                  ),
    .slv_aw_chan_t ( ser_aw_t               ),
    .mst_aw_chan_t ( mux_aw_t               ),
    .w_chan_t      ( w_t                    ),
    .slv_b_chan_t  ( ser_b_t                ),
    .mst_b_chan_t  ( mux_b_t                ),
    .slv_ar_chan_t ( ser_ar_t               ),
    .mst_ar_chan_t ( mux_ar_t               ),
    .slv_r_chan_t  ( ser_r_t                ),
    .mst_r_chan_t  ( mux_r_t                ),
    .slv_req_t     ( ser_req_t              ),
    .slv_resp_t    ( ser_resp_t             ),
    .mst_req_t     ( mux_req_t              ),
    .mst_resp_t    ( mux_resp_t             ),
    .NoSlvPorts    ( AxiMstPortMaxUniqIds   ),
    .MaxWTrans     ( AxiMstPortMaxTxnsPerId ),
    .FallThrough   ( 1'b0                   ),
    .SpillAw       ( 1'b1                   ),
    .SpillW        ( 1'b0                   ),
    .SpillB        ( 1'b0                   ),
    .SpillAr       ( 1'b1                   ),
    .SpillR        ( 1'b0                   )
  ) i_axi_mux (
    .clk_i,
    .rst_ni,
    .test_i      ( 1'b0                   ),
    .slv_reqs_i  ( from_serializer_reqs   ),
    .slv_resps_o ( from_serializer_resps  ),
    .mst_req_o   ( axi_mux_req            ),
    .mst_resp_i  ( axi_mux_resp           )
  );

  // Shift the ID one down if needed, as mux prepends IDs
  if (MuxIdWidth > 32'd1) begin : gen_id_shift
    always_comb begin
      `AXI_SET_REQ_STRUCT(mst_req_o, axi_mux_req)
      mst_req_o.aw.id = mst_id_t'(axi_mux_req.aw.id >> 32'd1);
      mst_req_o.ar.id = mst_id_t'(axi_mux_req.ar.id >> 32'd1);
      `AXI_SET_RESP_STRUCT(axi_mux_resp, mst_resp_i)
      axi_mux_resp.b.id = mux_id_t'(mst_resp_i.b.id << 32'd1);
      axi_mux_resp.r.id = mux_id_t'(mst_resp_i.r.id << 32'd1);
    end
  end else begin : gen_no_id_shift
    axi_id_prepend #(
      .NoBus             ( 32'd1              ),
      .AxiIdWidthSlvPort ( MuxIdWidth         ),
      .AxiIdWidthMstPort ( AxiMstPortIdWidth  ),
      .slv_aw_chan_t     ( mux_aw_t           ),
      .slv_w_chan_t      ( w_t                ),
      .slv_b_chan_t      ( mux_b_t            ),
      .slv_ar_chan_t     ( mux_ar_t           ),
      .slv_r_chan_t      ( mux_r_t            ),
      .mst_aw_chan_t     ( mst_aw_t           ),
      .mst_w_chan_t      ( w_t                ),
      .mst_b_chan_t      ( mst_b_t            ),
      .mst_ar_chan_t     ( mst_ar_t           ),
      .mst_r_chan_t      ( mst_r_t            )
    ) i_axi_id_prepend (
      .pre_id_i         ( '0                    ),
      .slv_aw_chans_i   ( axi_mux_req.aw        ),
      .slv_aw_valids_i  ( axi_mux_req.aw_valid  ),
      .slv_aw_readies_o ( axi_mux_resp.aw_ready ),
      .slv_w_chans_i    ( axi_mux_req.w         ),
      .slv_w_valids_i   ( axi_mux_req.w_valid   ),
      .slv_w_readies_o  ( axi_mux_resp.w_ready  ),
      .slv_b_chans_o    ( axi_mux_resp.b        ),
      .slv_b_valids_o   ( axi_mux_resp.b_valid  ),
      .slv_b_readies_i  ( axi_mux_req.b_ready   ),
      .slv_ar_chans_i   ( axi_mux_req.ar        ),
      .slv_ar_valids_i  ( axi_mux_req.ar_valid  ),
      .slv_ar_readies_o ( axi_mux_resp.ar_ready ),
      .slv_r_chans_o    ( axi_mux_resp.r        ),
      .slv_r_valids_o   ( axi_mux_resp.r_valid  ),
      .slv_r_readies_i  ( axi_mux_req.r_ready   ),
      .mst_aw_chans_o   ( mst_req_o.aw          ),
      .mst_aw_valids_o  ( mst_req_o.aw_valid    ),
      .mst_aw_readies_i ( mst_resp_i.aw_ready   ),
      .mst_w_chans_o    ( mst_req_o.w           ),
      .mst_w_valids_o   ( mst_req_o.w_valid     ),
      .mst_w_readies_i  ( mst_resp_i.w_ready    ),
      .mst_b_chans_i    ( mst_resp_i.b          ),
      .mst_b_valids_i   ( mst_resp_i.b_valid    ),
      .mst_b_readies_o  ( mst_req_o.b_ready     ),
      .mst_ar_chans_o   ( mst_req_o.ar          ),
      .mst_ar_valids_o  ( mst_req_o.ar_valid    ),
      .mst_ar_readies_i ( mst_resp_i.ar_ready   ),
      .mst_r_chans_i    ( mst_resp_i.r          ),
      .mst_r_valids_i   ( mst_resp_i.r_valid    ),
      .mst_r_readies_o  ( mst_req_o.r_ready     )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : p_assert
    assert(AxiMstPortMaxUniqIds > 32'd0)
      else $fatal(1, "AxiMstPortMaxUniqIds has to be > 0.");
    assert(2**(AxiMstPortIdWidth) >= AxiMstPortMaxUniqIds)
      else $fatal(1, "Not enought Id width on MST port to map all ID's.");
    assert(AxiSlvPortIdWidth > 32'd0)
      else $fatal(1, "Parameter AxiSlvPortIdWidth has to be larger than 0!");
    assert(AxiMstPortIdWidth)
      else $fatal(1, "Parameter AxiMstPortIdWidth has to be larger than 0!");
    assert(AxiMstPortIdWidth <= AxiSlvPortIdWidth)
      else $fatal(1, "Downsize implies that AxiMstPortIdWidth <= AxiSlvPortIdWidth!");
    assert($bits(slv_req_i.aw.addr) == $bits(mst_req_o.aw.addr))
      else $fatal(1, "AXI AW address widths are not equal!");
    assert($bits(slv_req_i.w.data) == $bits(mst_req_o.w.data))
      else $fatal(1, "AXI W data widths are not equal!");
    assert($bits(slv_req_i.ar.addr) == $bits(mst_req_o.ar.addr))
      else $fatal(1, "AXI AR address widths are not equal!");
    assert($bits(slv_resp_o.r.data) == $bits(mst_resp_i.r.data))
      else $fatal(1, "AXI R data widths are not equal!");
  end
  `endif
  // pragma translate_on
endmodule


/// Interface variant of [`axi_id_serialize`](module.axi_id_serialize).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_id_serialize_intf #(
  parameter int unsigned AXI_SLV_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_TXNS = 32'd0,
  parameter int unsigned AXI_MST_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_MST_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_MST_PORT_MAX_TXNS_PER_ID = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  parameter int unsigned AXI_USER_WIDTH = 32'd0
) (
  input  logic   clk_i,
  input  logic   rst_ni,
  AXI_BUS.Slave  slv,
  AXI_BUS.Master mst
);

  typedef logic [AXI_SLV_PORT_ID_WIDTH-1:0] slv_id_t;
  typedef logic [AXI_MST_PORT_ID_WIDTH-1:0] mst_id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]        addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]        data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]      strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]        user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_t, data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_t, w_t, slv_ar_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_t, slv_r_t)

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_t, mst_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_t, data_t, mst_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_t, w_t, mst_ar_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_t, mst_r_t)

  slv_req_t  slv_req;
  slv_resp_t slv_resp;
  mst_req_t  mst_req;
  mst_resp_t mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_id_serialize #(
    .AxiSlvPortIdWidth      ( AXI_SLV_PORT_ID_WIDTH         ),
    .AxiSlvPortMaxTxns      ( AXI_SLV_PORT_MAX_TXNS         ),
    .AxiMstPortIdWidth      ( AXI_MST_PORT_ID_WIDTH         ),
    .AxiMstPortMaxUniqIds   ( AXI_MST_PORT_MAX_UNIQ_IDS     ),
    .AxiMstPortMaxTxnsPerId ( AXI_MST_PORT_MAX_TXNS_PER_ID  ),
    .AxiAddrWidth           ( AXI_ADDR_WIDTH                ),
    .AxiDataWidth           ( AXI_DATA_WIDTH                ),
    .AxiUserWidth           ( AXI_USER_WIDTH                ),
    .slv_req_t              ( slv_req_t                     ),
    .slv_resp_t             ( slv_resp_t                    ),
    .mst_req_t              ( mst_req_t                     ),
    .mst_resp_t             ( mst_resp_t                    )
  ) i_axi_id_serialize (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert (slv.AXI_ID_WIDTH   == AXI_SLV_PORT_ID_WIDTH);
    assert (slv.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
    assert (slv.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
    assert (slv.AXI_USER_WIDTH == AXI_USER_WIDTH);
    assert (mst.AXI_ID_WIDTH   == AXI_MST_PORT_ID_WIDTH);
    assert (mst.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
    assert (mst.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
    assert (mst.AXI_USER_WIDTH == AXI_USER_WIDTH);
  end
`endif
// pragma translate_on
endmodule
