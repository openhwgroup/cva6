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
// - Tim Fischer <fischeti@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Vikram Jain <jvikram@iis.ee.ethz.ch>

`include "axi/typedef.svh"

/// AXI Crosspoint (XP) with homomorphous slave and master ports.
module axi_xp #(
  // Atomic operations settings
  parameter bit  ATOPs = 1'b1,
  // xbar configuration
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  /// Number of slave ports.
  parameter int unsigned NumSlvPorts = 32'd0,
  /// Number of master ports.
  parameter int unsigned NumMstPorts = 32'd0,
  /// Connectivity from a slave port to the master ports.  A `1'b1` in `Connectivity[i][j]` means
  /// that slave port `i` is connected to master port `j`.  By default, all slave ports are
  /// connected to all master ports.
  parameter bit [NumSlvPorts-1:0][NumMstPorts-1:0] Connectivity = '1,
  /// Address width of all ports.
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// Data width of all ports.
  parameter int unsigned AxiDataWidth = 32'd0,
  /// ID width of all ports.
  parameter int unsigned AxiIdWidth = 32'd0,
  /// User signal width of all ports.
  parameter int unsigned AxiUserWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at each slave port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// It is legal for upstream to have transactions with more unique IDs than the maximum given by
  /// this parameter in flight, but a transaction exceeding the maximum will be stalled until all
  /// transactions of another ID complete.
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the slave port.
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds <= 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to [`axi_id_remap` as `AxiMaxTxnsPerId`
  /// parameter](module.axi_id_remap#parameter.AxiMaxTxnsPerId).
  parameter int unsigned AxiSlvPortMaxTxnsPerId = 32'd0,
  /// Maximum number of in-flight transactions at the slave port.  Reads and writes are counted
  /// separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiSlvPortMaxTxns).
  parameter int unsigned AxiSlvPortMaxTxns = 32'd0,
  /// Maximum number of different IDs that can be in flight at the master port.  Reads and writes
  /// are counted separately (except for ATOPs, which count as both read and write).
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiMstPortMaxUniqIds).
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID at the master port.
  ///
  /// This parameter is only relevant if `AxiSlvPortMaxUniqIds > 2**AxiMstPortIdWidth`.  In that
  /// case, this parameter is passed to
  /// [`axi_id_serialize`](module.axi_id_serialize#parameter.AxiMstPortMaxTxnsPerId).
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd0,
  /// Number of rules in the address map.
  parameter int unsigned NumAddrRules = 32'd0,
  /// Request struct type of the AXI4+ATOP
  parameter type axi_req_t  = logic,
  /// Response struct type of the AXI4+ATOP
  parameter type axi_resp_t = logic,
  /// Rule type (see documentation of `axi_xbar` for details).
  parameter type rule_t = axi_pkg::xbar_rule_64_t
) (
  /// Rising-edge clock of all ports
  input  logic                          clk_i,
  /// Asynchronous reset, active low
  input  logic                          rst_ni,
  /// Test mode enable
  input  logic                          test_en_i,
  /// Slave ports request
  input  axi_req_t  [NumSlvPorts-1:0]   slv_req_i,
  /// Slave ports response
  output axi_resp_t [NumSlvPorts-1:0]   slv_resp_o,
  /// Master ports request
  output axi_req_t  [NumMstPorts-1:0]   mst_req_o,
  /// Master ports response
  input  axi_resp_t [NumMstPorts-1:0]   mst_resp_i,
  /// Address map for transferring transactions from slave to master ports
  input  rule_t     [NumAddrRules-1:0]  addr_map_i
);

  // The master port of the Xbar has a different ID width than the slave ports.
  parameter int unsigned AxiXbarIdWidth = AxiIdWidth + $clog2(NumSlvPorts);
  typedef logic [AxiAddrWidth-1:0]    addr_t;
  typedef logic [AxiDataWidth-1:0]    data_t;
  typedef logic [AxiIdWidth-1:0]      id_t;
  typedef logic [AxiXbarIdWidth-1:0]  xbar_id_t;
  typedef logic [AxiDataWidth/8-1:0]  strb_t;
  typedef logic [AxiUserWidth-1:0]    user_t;


  `AXI_TYPEDEF_ALL(xp, addr_t, id_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_ALL(xbar, addr_t, xbar_id_t, data_t, strb_t, user_t)

  xbar_req_t  [NumMstPorts-1:0] xbar_req;
  xbar_resp_t [NumMstPorts-1:0] xbar_resp;

  axi_xbar #(
    .Cfg            ( Cfg             ),
    .ATOPs          ( ATOPs           ),
    .Connectivity   ( Connectivity    ),
    .slv_aw_chan_t  ( xp_aw_chan_t    ),
    .mst_aw_chan_t  ( xbar_aw_chan_t  ),
    .w_chan_t       ( xp_w_chan_t     ),
    .slv_b_chan_t   ( xp_b_chan_t     ),
    .mst_b_chan_t   ( xbar_b_chan_t   ),
    .slv_ar_chan_t  ( xp_ar_chan_t    ),
    .mst_ar_chan_t  ( xbar_ar_chan_t  ),
    .slv_r_chan_t   ( xp_r_chan_t     ),
    .mst_r_chan_t   ( xbar_r_chan_t   ),
    .slv_req_t      ( axi_req_t       ),
    .slv_resp_t     ( axi_resp_t      ),
    .mst_req_t      ( xbar_req_t      ),
    .mst_resp_t     ( xbar_resp_t     ),
    .rule_t         ( rule_t          )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i                 ( test_en_i                               ),
    .slv_ports_req_i        ( slv_req_i                               ),
    .slv_ports_resp_o       ( slv_resp_o                              ),
    .mst_ports_req_o        ( xbar_req                                ),
    .mst_ports_resp_i       ( xbar_resp                               ),
    .addr_map_i,
    .en_default_mst_port_i  ( '0                                      ),
    .default_mst_port_i     ( '0                                      )
  );

  for (genvar i = 0; i < NumMstPorts; i++) begin : gen_remap
    axi_id_remap #(
      .AxiSlvPortIdWidth    ( AxiXbarIdWidth         ),
      .AxiSlvPortMaxUniqIds ( AxiSlvPortMaxUniqIds   ),
      .AxiMaxTxnsPerId      ( AxiSlvPortMaxTxnsPerId ),
      .AxiMstPortIdWidth    ( AxiIdWidth             ),
      .slv_req_t            ( xbar_req_t             ),
      .slv_resp_t           ( xbar_resp_t            ),
      .mst_req_t            ( axi_req_t                  ),
      .mst_resp_t           ( axi_resp_t                 )
    ) i_axi_id_remap (
      .clk_i,
      .rst_ni,
      .slv_req_i  ( xbar_req[i]   ),
      .slv_resp_o ( xbar_resp[i]  ),
      .mst_req_o  ( mst_req_o[i]  ),
      .mst_resp_i ( mst_resp_i[i] )
    );
  end

endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_xp_intf
import cf_math_pkg::idx_width;
#(
  parameter bit  ATOPs = 1'b1,
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  parameter int unsigned NumSlvPorts = 32'd0,
  parameter int unsigned NumMstPorts = 32'd0,
  parameter bit [NumSlvPorts-1:0][NumMstPorts-1:0] Connectivity = '1,
  parameter int unsigned AxiAddrWidth = 32'd0,
  parameter int unsigned AxiDataWidth = 32'd0,
  parameter int unsigned AxiIdWidth = 32'd0,
  parameter int unsigned AxiUserWidth = 32'd0,
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd0,
  parameter int unsigned AxiSlvPortMaxTxnsPerId = 32'd0,
  parameter int unsigned AxiSlvPortMaxTxns = 32'd0,
  parameter int unsigned AxiMstPortMaxUniqIds = 32'd0,
  parameter int unsigned AxiMstPortMaxTxnsPerId = 32'd0,
  parameter int unsigned NumAddrRules = 32'd0,
  parameter type rule_t = axi_pkg::xbar_rule_64_t
) (
  input  logic                       clk_i,
  input  logic                       rst_ni,
  input  logic                       test_en_i,
  AXI_BUS.Slave                      slv_ports [NumSlvPorts-1:0],
  AXI_BUS.Master                     mst_ports [NumMstPorts-1:0],
  input  rule_t  [NumAddrRules-1:0]  addr_map_i
);

  // localparam int unsigned AxiIdWidthMstPorts = AxiIdWidth + $clog2(NoSlvPorts);

  typedef logic [AxiIdWidth         -1:0] id_t;
  typedef logic [AxiAddrWidth       -1:0] addr_t;
  typedef logic [AxiDataWidth       -1:0] data_t;
  typedef logic [AxiDataWidth/8     -1:0] strb_t;
  typedef logic [AxiUserWidth       -1:0] user_t;

  `AXI_TYPEDEF_ALL(axi, addr_t, id_t, data_t, strb_t, user_t)

  axi_req_t   [NumMstPorts-1:0]  mst_reqs;
  axi_resp_t  [NumMstPorts-1:0]  mst_resps;
  axi_req_t   [NumSlvPorts-1:0]  slv_reqs;
  axi_resp_t  [NumSlvPorts-1:0]  slv_resps;

  for (genvar i = 0; i < NumMstPorts; i++) begin : gen_assign_mst
    `AXI_ASSIGN_FROM_REQ(mst_ports[i], mst_reqs[i])
    `AXI_ASSIGN_TO_RESP(mst_resps[i], mst_ports[i])
  end

  for (genvar i = 0; i < NumSlvPorts; i++) begin : gen_assign_slv
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv_ports[i])
    `AXI_ASSIGN_FROM_RESP(slv_ports[i], slv_resps[i])
  end

  axi_xp #(
    .ATOPs                   ( ATOPs         ),
    .Cfg                     ( Cfg           ),
    .NumSlvPorts             ( NumSlvPorts    ),
    .NumMstPorts             ( NumMstPorts    ),
    .Connectivity            ( Connectivity  ),
    .AxiAddrWidth            ( AxiAddrWidth  ),
    .AxiDataWidth            ( AxiDataWidth  ),
    .AxiIdWidth              ( AxiIdWidth    ),
    .AxiUserWidth            ( AxiUserWidth  ),
    .AxiSlvPortMaxUniqIds    ( AxiSlvPortMaxUniqIds   ),
    .AxiSlvPortMaxTxnsPerId  ( AxiSlvPortMaxTxnsPerId ),
    .AxiSlvPortMaxTxns       ( AxiSlvPortMaxTxns      ),
    .AxiMstPortMaxUniqIds    ( AxiMstPortMaxUniqIds   ),
    .AxiMstPortMaxTxnsPerId  ( AxiMstPortMaxTxnsPerId ),
    .NumAddrRules            ( NumAddrRules            ),
    .axi_req_t               ( axi_req_t     ),
    .axi_resp_t              ( axi_resp_t    ),
    .rule_t                  ( rule_t        )
  ) i_xp (
    .clk_i,
    .rst_ni,
    .test_en_i,
    .slv_req_i  (slv_reqs ),
    .slv_resp_o (slv_resps),
    .mst_req_o  (mst_reqs ),
    .mst_resp_i (mst_resps),
    .addr_map_i
  );

endmodule
