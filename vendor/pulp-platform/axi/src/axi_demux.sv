// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "common_cells/assertions.svh"
`include "common_cells/registers.svh"

`ifdef QUESTA
// Derive `TARGET_VSIM`, which is used for tool-specific workarounds in this file, from `QUESTA`,
// which is automatically set in Questa.
`define TARGET_VSIM
`endif

/// Demultiplex one AXI4+ATOP slave port to multiple AXI4+ATOP master ports.
///
/// The AW and AR slave channels each have a `select` input to determine to which master port the
/// current request is sent.  The `select` can, for example, be driven by an address decoding module
/// to map address ranges to different AXI slaves.
///
/// ## Design overview
///
/// ![Block diagram](module.axi_demux.png "Block diagram")
///
/// Beats on the W channel are routed by demultiplexer according to the selection for the
/// corresponding AW beat.  This relies on the AXI property that W bursts must be sent in the same
/// order as AW beats and beats from different W bursts may not be interleaved.
///
/// Beats on the B and R channel are multiplexed from the master ports to the slave port with
/// a round-robin arbitration tree.
module axi_demux #(
  parameter int unsigned AxiIdWidth     = 32'd0,
  parameter bit          AtopSupport    = 1'b1,
  parameter type         aw_chan_t      = logic,
  parameter type         w_chan_t       = logic,
  parameter type         b_chan_t       = logic,
  parameter type         ar_chan_t      = logic,
  parameter type         r_chan_t       = logic,
  parameter type         axi_req_t      = logic,
  parameter type         axi_resp_t     = logic,
  parameter int unsigned NoMstPorts     = 32'd0,
  parameter int unsigned MaxTrans       = 32'd8,
  parameter int unsigned AxiLookBits    = 32'd3,
  parameter bit          UniqueIds      = 1'b0,
  parameter bit          SpillAw        = 1'b1,
  parameter bit          SpillW         = 1'b0,
  parameter bit          SpillB         = 1'b0,
  parameter bit          SpillAr        = 1'b1,
  parameter bit          SpillR         = 1'b0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter int unsigned SelectWidth    = (NoMstPorts > 32'd1) ? $clog2(NoMstPorts) : 32'd1,
  parameter type         select_t       = logic [SelectWidth-1:0]
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          test_i,
  // Slave Port
  input  axi_req_t                      slv_req_i,
  input  select_t                       slv_aw_select_i,
  input  select_t                       slv_ar_select_i,
  output axi_resp_t                     slv_resp_o,
  // Master Ports
  output axi_req_t    [NoMstPorts-1:0]  mst_reqs_o,
  input  axi_resp_t   [NoMstPorts-1:0]  mst_resps_i
);

  axi_req_t slv_req_cut;
  axi_resp_t slv_resp_cut;

  logic slv_aw_ready_chan, slv_aw_ready_sel;
  logic slv_aw_valid_chan, slv_aw_valid_sel;

  logic slv_ar_ready_chan, slv_ar_ready_sel;
  logic slv_ar_valid_chan, slv_ar_valid_sel;

  select_t slv_aw_select, slv_ar_select;

  spill_register #(
    .T       ( aw_chan_t  ),
    .Bypass  ( ~SpillAw   )
  ) i_aw_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_req_i.aw_valid    ),
    .ready_o ( slv_aw_ready_chan     ),
    .data_i  ( slv_req_i.aw          ),
    .valid_o ( slv_aw_valid_chan     ),
    .ready_i ( slv_resp_cut.aw_ready ),
    .data_o  ( slv_req_cut.aw        )
  );
  spill_register #(
    .T       ( select_t ),
    .Bypass  ( ~SpillAw )
  ) i_aw_select_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_req_i.aw_valid    ),
    .ready_o ( slv_aw_ready_sel      ),
    .data_i  ( slv_aw_select_i       ),
    .valid_o ( slv_aw_valid_sel      ),
    .ready_i ( slv_resp_cut.aw_ready ),
    .data_o  ( slv_aw_select         )
  );

  assign slv_resp_o.aw_ready  = slv_aw_ready_chan & slv_aw_ready_sel;
  assign slv_req_cut.aw_valid = slv_aw_valid_chan & slv_aw_valid_sel;

  spill_register #(
    .T       ( w_chan_t  ),
    .Bypass  ( ~SpillW   )
  ) i_w_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_req_i.w_valid    ),
    .ready_o ( slv_resp_o.w_ready   ),
    .data_i  ( slv_req_i.w          ),
    .valid_o ( slv_req_cut.w_valid  ),
    .ready_i ( slv_resp_cut.w_ready ),
    .data_o  ( slv_req_cut.w        )
  );
  spill_register #(
    .T       ( ar_chan_t  ),
    .Bypass  ( ~SpillAr   )
  ) i_ar_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_req_i.ar_valid    ),
    .ready_o ( slv_ar_ready_chan     ),
    .data_i  ( slv_req_i.ar          ),
    .valid_o ( slv_ar_valid_chan     ),
    .ready_i ( slv_resp_cut.ar_ready ),
    .data_o  ( slv_req_cut.ar        )
  );
  spill_register #(
    .T       ( select_t ),
    .Bypass  ( ~SpillAr )
  ) i_ar_sel_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_req_i.ar_valid    ),
    .ready_o ( slv_ar_ready_sel      ),
    .data_i  ( slv_ar_select_i       ),
    .valid_o ( slv_ar_valid_sel      ),
    .ready_i ( slv_resp_cut.ar_ready ),
    .data_o  ( slv_ar_select         )
  );

  assign slv_resp_o.ar_ready  = slv_ar_ready_chan & slv_ar_ready_sel;
  assign slv_req_cut.ar_valid = slv_ar_valid_chan & slv_ar_valid_sel;

  spill_register #(
    .T       ( b_chan_t ),
    .Bypass  ( ~SpillB  )
  ) i_b_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_resp_cut.b_valid ),
    .ready_o ( slv_req_cut.b_ready  ),
    .data_i  ( slv_resp_cut.b       ),
    .valid_o ( slv_resp_o.b_valid   ),
    .ready_i ( slv_req_i.b_ready    ),
    .data_o  ( slv_resp_o.b         )
  );
  spill_register #(
    .T       ( r_chan_t ),
    .Bypass  ( ~SpillR  )
  ) i_r_spill_reg (
    .clk_i,
    .rst_ni,
    .valid_i ( slv_resp_cut.r_valid ),
    .ready_o ( slv_req_cut.r_ready  ),
    .data_i  ( slv_resp_cut.r       ),
    .valid_o ( slv_resp_o.r_valid   ),
    .ready_i ( slv_req_i.r_ready    ),
    .data_o  ( slv_resp_o.r         )
  );

  axi_demux_simple #(
    .AxiIdWidth ( AxiIdWidth  ),
    .AtopSupport( AtopSupport ),
    .axi_req_t  ( axi_req_t   ),
    .axi_resp_t ( axi_resp_t  ),
    .NoMstPorts ( NoMstPorts  ),
    .MaxTrans   ( MaxTrans    ),
    .AxiLookBits( AxiLookBits ),
    .UniqueIds  ( UniqueIds   )
  ) i_demux_simple (
    .clk_i,
    .rst_ni,
    .test_i,

    .slv_req_i       ( slv_req_cut   ),
    .slv_aw_select_i ( slv_aw_select ),
    .slv_ar_select_i ( slv_ar_select ),
    .slv_resp_o      ( slv_resp_cut  ),
    .mst_reqs_o      ( mst_reqs_o    ),
    .mst_resps_i     ( mst_resps_i   )
  );

endmodule

// interface wrapper
`include "axi/assign.svh"
`include "axi/typedef.svh"
module axi_demux_intf #(
  parameter int unsigned AXI_ID_WIDTH     = 32'd0, // Synopsys DC requires default value for params
  parameter bit          ATOP_SUPPORT     = 1'b1,
  parameter int unsigned AXI_ADDR_WIDTH   = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH   = 32'd0,
  parameter int unsigned AXI_USER_WIDTH   = 32'd0,
  parameter int unsigned NO_MST_PORTS     = 32'd3,
  parameter int unsigned MAX_TRANS        = 32'd8,
  parameter int unsigned AXI_LOOK_BITS    = 32'd3,
  parameter bit          UNIQUE_IDS       = 1'b0,
  parameter bit          SPILL_AW         = 1'b1,
  parameter bit          SPILL_W          = 1'b0,
  parameter bit          SPILL_B          = 1'b0,
  parameter bit          SPILL_AR         = 1'b1,
  parameter bit          SPILL_R          = 1'b0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter int unsigned SELECT_WIDTH   = (NO_MST_PORTS > 32'd1) ? $clog2(NO_MST_PORTS) : 32'd1,
  parameter type         select_t       = logic [SELECT_WIDTH-1:0] // MST port select type
) (
  input  logic    clk_i,                 // Clock
  input  logic    rst_ni,                // Asynchronous reset active low
  input  logic    test_i,                // Testmode enable
  input  select_t slv_aw_select_i,       // has to be stable, when aw_valid
  input  select_t slv_ar_select_i,       // has to be stable, when ar_valid
  AXI_BUS.Slave   slv,                   // slave port
  AXI_BUS.Master  mst [NO_MST_PORTS-1:0] // master ports
);

  typedef logic [AXI_ID_WIDTH-1:0]       id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t                     slv_req;
  axi_resp_t                    slv_resp;
  axi_req_t  [NO_MST_PORTS-1:0] mst_req;
  axi_resp_t [NO_MST_PORTS-1:0] mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  for (genvar i = 0; i < NO_MST_PORTS; i++) begin : gen_assign_mst_ports
    `AXI_ASSIGN_FROM_REQ(mst[i], mst_req[i])
    `AXI_ASSIGN_TO_RESP(mst_resp[i], mst[i])
  end

  axi_demux #(
    .AxiIdWidth     ( AXI_ID_WIDTH  ), // ID Width
    .AtopSupport    ( ATOP_SUPPORT  ),
    .aw_chan_t      (  aw_chan_t    ), // AW Channel Type
    .w_chan_t       (   w_chan_t    ), //  W Channel Type
    .b_chan_t       (   b_chan_t    ), //  B Channel Type
    .ar_chan_t      (  ar_chan_t    ), // AR Channel Type
    .r_chan_t       (   r_chan_t    ), //  R Channel Type
    .axi_req_t      (  axi_req_t    ),
    .axi_resp_t     ( axi_resp_t    ),
    .NoMstPorts     ( NO_MST_PORTS  ),
    .MaxTrans       ( MAX_TRANS     ),
    .AxiLookBits    ( AXI_LOOK_BITS ),
    .UniqueIds      ( UNIQUE_IDS    ),
    .SpillAw        ( SPILL_AW      ),
    .SpillW         ( SPILL_W       ),
    .SpillB         ( SPILL_B       ),
    .SpillAr        ( SPILL_AR      ),
    .SpillR         ( SPILL_R       )
  ) i_axi_demux (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    .test_i,  // Testmode enable
    // slave port
    .slv_req_i       ( slv_req         ),
    .slv_aw_select_i ( slv_aw_select_i ),
    .slv_ar_select_i ( slv_ar_select_i ),
    .slv_resp_o      ( slv_resp        ),
    // master port
    .mst_reqs_o      ( mst_req         ),
    .mst_resps_i     ( mst_resp        )
  );
endmodule
