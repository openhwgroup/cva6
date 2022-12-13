// Copyright (c) 2020 ETH Zurich and University of Bologna.
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

// axi_lite_xbar: Fully-connected AXI4-Lite crossbar.
// See `doc/axi_lite_xbar.md` for the documentation,
// including the definition of parameters and ports.

`include "axi/typedef.svh"

module axi_lite_xbar #(
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  parameter type aw_chan_t          = logic,
  parameter type  w_chan_t          = logic,
  parameter type  b_chan_t          = logic,
  parameter type ar_chan_t          = logic,
  parameter type  r_chan_t          = logic,
  parameter type     req_t          = logic,
  parameter type    resp_t          = logic,
  parameter type    rule_t          = axi_pkg::xbar_rule_64_t,
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter int unsigned MstIdxWidth = (Cfg.NoMstPorts > 32'd1) ? $clog2(Cfg.NoMstPorts) : 32'd1
) (
  input  logic                                        clk_i,
  input  logic                                        rst_ni,
  input  logic                                        test_i,
  input  req_t  [Cfg.NoSlvPorts-1:0]                  slv_ports_req_i,
  output resp_t [Cfg.NoSlvPorts-1:0]                  slv_ports_resp_o,
  output req_t  [Cfg.NoMstPorts-1:0]                  mst_ports_req_o,
  input  resp_t [Cfg.NoMstPorts-1:0]                  mst_ports_resp_i,
  input  rule_t [Cfg.NoAddrRules-1:0]                 addr_map_i,
  input  logic  [Cfg.NoSlvPorts-1:0]                  en_default_mst_port_i,
  input  logic  [Cfg.NoSlvPorts-1:0][MstIdxWidth-1:0] default_mst_port_i
);

  typedef logic [Cfg.AxiAddrWidth-1:0]   addr_t;
  typedef logic [Cfg.AxiDataWidth-1:0]   data_t;
  typedef logic [Cfg.AxiDataWidth/8-1:0] strb_t;
  // to account for the decoding error slave
  typedef logic [$clog2(Cfg.NoMstPorts + 1)-1:0] mst_port_idx_t;
  // full AXI typedef for the decode error slave, id_t and user_t are logic and will be
  // removed during logic optimization as they are stable
  `AXI_TYPEDEF_AW_CHAN_T(full_aw_chan_t, addr_t, logic, logic)
  `AXI_TYPEDEF_W_CHAN_T(full_w_chan_t, data_t, strb_t, logic)
  `AXI_TYPEDEF_B_CHAN_T(full_b_chan_t, logic, logic)
  `AXI_TYPEDEF_AR_CHAN_T(full_ar_chan_t, addr_t, logic, logic)
  `AXI_TYPEDEF_R_CHAN_T(full_r_chan_t, data_t, logic, logic)
  `AXI_TYPEDEF_REQ_T(full_req_t, full_aw_chan_t, full_w_chan_t, full_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(full_resp_t, full_b_chan_t, full_r_chan_t)

  // signals from the axi_lite_demuxes, one index more for decode error routing
  req_t  [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_reqs;
  resp_t [Cfg.NoSlvPorts-1:0][Cfg.NoMstPorts:0] slv_resps;

  // signals into the axi_lite_muxes, are of type slave as the multiplexer extends the ID
  req_t  [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_reqs;
  resp_t [Cfg.NoMstPorts-1:0][Cfg.NoSlvPorts-1:0] mst_resps;

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_slv_port_demux
    logic [MstIdxWidth-1:0] dec_aw,        dec_ar;
    mst_port_idx_t          slv_aw_select, slv_ar_select;
    logic                   dec_aw_error;
    logic                   dec_ar_error;

    full_req_t  decerr_req;
    full_resp_t decerr_resp;

    addr_decode #(
      .NoIndices  ( Cfg.NoMstPorts  ),
      .NoRules    ( Cfg.NoAddrRules ),
      .addr_t     ( addr_t          ),
      .rule_t     ( rule_t          )
    ) i_axi_aw_decode (
      .addr_i           ( slv_ports_req_i[i].aw.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_aw                     ),
      .dec_valid_o      ( /*not used*/               ),
      .dec_error_o      ( dec_aw_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_port_i[i]      )
    );

    addr_decode #(
      .NoIndices  ( Cfg.NoMstPorts  ),
      .addr_t     ( addr_t          ),
      .NoRules    ( Cfg.NoAddrRules ),
      .rule_t     ( rule_t          )
    ) i_axi_ar_decode (
      .addr_i           ( slv_ports_req_i[i].ar.addr ),
      .addr_map_i       ( addr_map_i                 ),
      .idx_o            ( dec_ar                     ),
      .dec_valid_o      ( /*not used*/               ),
      .dec_error_o      ( dec_ar_error               ),
      .en_default_idx_i ( en_default_mst_port_i[i]   ),
      .default_idx_i    ( default_mst_port_i[i]      )
    );

    assign slv_aw_select = (dec_aw_error) ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_aw);
    assign slv_ar_select = (dec_ar_error) ?
        mst_port_idx_t'(Cfg.NoMstPorts) : mst_port_idx_t'(dec_ar);

    // make sure that the default slave does not get changed, if there is an unserved Ax
    // pragma translate_off
    `ifndef VERILATOR
    default disable iff (~rst_ni);
    default_aw_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   enable, when there is an unserved Aw beat. Slave Port: %0d", i));
    default_aw_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].aw_valid && !slv_ports_resp_o[i].aw_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Aw beat. Slave Port: %0d", i));
    default_ar_mst_port_en: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(en_default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the enable, when\
                                   there is an unserved Ar beat. Slave Port: %0d", i));
    default_ar_mst_port: assert property(
      @(posedge clk_i) (slv_ports_req_i[i].ar_valid && !slv_ports_resp_o[i].ar_ready)
          |=> $stable(default_mst_port_i[i]))
        else $fatal (1, $sformatf("It is not allowed to change the default mst port\
                                   when there is an unserved Ar beat. Slave Port: %0d", i));
    `endif
    // pragma translate_on
    axi_lite_demux #(
      .aw_chan_t      ( aw_chan_t          ),  // AW Channel Type
      .w_chan_t       (  w_chan_t          ),  //  W Channel Type
      .b_chan_t       (  b_chan_t          ),  //  B Channel Type
      .ar_chan_t      ( ar_chan_t          ),  // AR Channel Type
      .r_chan_t       (  r_chan_t          ),  //  R Channel Type
      .req_t          ( req_t              ),
      .resp_t         ( resp_t             ),
      .NoMstPorts     ( Cfg.NoMstPorts + 1 ),
      .MaxTrans       ( Cfg.MaxMstTrans    ),
      .FallThrough    ( Cfg.FallThrough    ),
      .SpillAw        ( Cfg.LatencyMode[9] ),
      .SpillW         ( Cfg.LatencyMode[8] ),
      .SpillB         ( Cfg.LatencyMode[7] ),
      .SpillAr        ( Cfg.LatencyMode[6] ),
      .SpillR         ( Cfg.LatencyMode[5] )
    ) i_axi_lite_demux (
      .clk_i,   // Clock
      .rst_ni,  // Asynchronous reset active low
      .test_i,  // Testmode enable
      .slv_req_i       ( slv_ports_req_i[i]  ),
      .slv_aw_select_i ( slv_aw_select       ),
      .slv_ar_select_i ( slv_ar_select       ),
      .slv_resp_o      ( slv_ports_resp_o[i] ),
      .mst_reqs_o      ( slv_reqs[i]         ),
      .mst_resps_i     ( slv_resps[i]        )
    );

    // connect the decode error module to the last index of the demux master port
    // typedef as the decode error slave uses full axi
    axi_lite_to_axi #(
      .AxiDataWidth ( Cfg.AxiDataWidth  ),
      .req_lite_t   ( req_t             ),
      .resp_lite_t  ( resp_t            ),
      .req_t        ( full_req_t        ),
      .resp_t       ( full_resp_t       )
    ) i_dec_err_conv (
      .slv_req_lite_i  ( slv_reqs[i][Cfg.NoMstPorts]  ),
      .slv_resp_lite_o ( slv_resps[i][Cfg.NoMstPorts] ),
      .slv_aw_cache_i  ( 4'd0                         ),
      .slv_ar_cache_i  ( 4'd0                         ),
      .mst_req_o       ( decerr_req                   ),
      .mst_resp_i      ( decerr_resp                  )
    );

    axi_err_slv #(
      .AxiIdWidth  ( 32'd1                ), // ID width is one as defined as logic above
      .req_t       ( full_req_t           ), // AXI request struct
      .resp_t      ( full_resp_t          ), // AXI response struct
      .Resp        ( axi_pkg::RESP_DECERR ),
      .ATOPs       ( 1'b0                 ), // no ATOPs in AXI4-Lite
      .MaxTrans    ( 1                    )  // Transactions terminate at this slave, and AXI4-Lite
                                             // transactions have only a single beat.
    ) i_axi_err_slv (
      .clk_i      ( clk_i       ),  // Clock
      .rst_ni     ( rst_ni      ),  // Asynchronous reset active low
      .test_i     ( test_i      ),  // Testmode enable
      // slave port
      .slv_req_i  ( decerr_req  ),
      .slv_resp_o ( decerr_resp )
    );
  end

  // cross all channels
  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_xbar_slv_cross
    for (genvar j = 0; j < Cfg.NoMstPorts; j++) begin : gen_xbar_mst_cross
      assign mst_reqs[j][i]  = slv_reqs[i][j];
      assign slv_resps[i][j] = mst_resps[j][i];
    end
  end

  for (genvar i = 0; i < Cfg.NoMstPorts; i++) begin : gen_mst_port_mux
    axi_lite_mux #(
      .aw_chan_t   ( aw_chan_t          ), // AW Channel Type
      .w_chan_t    (  w_chan_t          ), //  W Channel Type
      .b_chan_t    (  b_chan_t          ), //  B Channel Type
      .ar_chan_t   ( ar_chan_t          ), // AR Channel Type
      .r_chan_t    (  r_chan_t          ), //  R Channel Type
      .req_t       ( req_t              ),
      .resp_t      ( resp_t             ),
      .NoSlvPorts  ( Cfg.NoSlvPorts     ), // Number of Masters for the module
      .MaxTrans    ( Cfg.MaxSlvTrans    ),
      .FallThrough ( Cfg.FallThrough    ),
      .SpillAw     ( Cfg.LatencyMode[4] ),
      .SpillW      ( Cfg.LatencyMode[3] ),
      .SpillB      ( Cfg.LatencyMode[2] ),
      .SpillAr     ( Cfg.LatencyMode[1] ),
      .SpillR      ( Cfg.LatencyMode[0] )
    ) i_axi_lite_mux (
      .clk_i,  // Clock
      .rst_ni, // Asynchronous reset active low
      .test_i, // Test Mode enable
      .slv_reqs_i  ( mst_reqs[i]         ),
      .slv_resps_o ( mst_resps[i]        ),
      .mst_req_o   ( mst_ports_req_o[i]  ),
      .mst_resp_i  ( mst_ports_resp_i[i] )
    );
  end
endmodule

`include "axi/assign.svh"

module axi_lite_xbar_intf #(
  parameter axi_pkg::xbar_cfg_t Cfg = '0,
  parameter type rule_t             = axi_pkg::xbar_rule_64_t
) (
  input  logic                                                    clk_i,
  input  logic                                                    rst_ni,
  input  logic                                                    test_i,
  AXI_LITE.Slave                                                  slv_ports [Cfg.NoSlvPorts-1:0],
  AXI_LITE.Master                                                 mst_ports [Cfg.NoMstPorts-1:0],
  input  rule_t [Cfg.NoAddrRules-1:0]                             addr_map_i,
  input  logic  [Cfg.NoSlvPorts-1:0]                              en_default_mst_port_i,
  input  logic  [Cfg.NoSlvPorts-1:0][$clog2(Cfg.NoMstPorts)-1:0]  default_mst_port_i
);

  typedef logic [Cfg.AxiAddrWidth       -1:0] addr_t;
  typedef logic [Cfg.AxiDataWidth       -1:0] data_t;
  typedef logic [Cfg.AxiDataWidth/8     -1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t   [Cfg.NoMstPorts-1:0]  mst_reqs;
  resp_t  [Cfg.NoMstPorts-1:0]  mst_resps;
  req_t   [Cfg.NoSlvPorts-1:0]  slv_reqs;
  resp_t  [Cfg.NoSlvPorts-1:0]  slv_resps;

  for (genvar i = 0; i < Cfg.NoMstPorts; i++) begin : gen_assign_mst
    `AXI_LITE_ASSIGN_FROM_REQ(mst_ports[i], mst_reqs[i])
    `AXI_LITE_ASSIGN_TO_RESP(mst_resps[i], mst_ports[i])
  end

  for (genvar i = 0; i < Cfg.NoSlvPorts; i++) begin : gen_assign_slv
    `AXI_LITE_ASSIGN_TO_REQ(slv_reqs[i], slv_ports[i])
    `AXI_LITE_ASSIGN_FROM_RESP(slv_ports[i], slv_resps[i])
  end

  axi_lite_xbar #(
    .Cfg  (Cfg),
    .aw_chan_t  ( aw_chan_t ),
    .w_chan_t   ( w_chan_t  ),
    .b_chan_t   ( b_chan_t  ),
    .ar_chan_t  ( ar_chan_t ),
    .r_chan_t   ( r_chan_t  ),
    .req_t      ( req_t     ),
    .resp_t     ( resp_t    ),
    .rule_t     ( rule_t    )
  ) i_xbar (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_ports_req_i  (slv_reqs ),
    .slv_ports_resp_o (slv_resps),
    .mst_ports_req_o  (mst_reqs ),
    .mst_ports_resp_i (mst_resps),
    .addr_map_i,
    .en_default_mst_port_i,
    .default_mst_port_i
  );

endmodule
