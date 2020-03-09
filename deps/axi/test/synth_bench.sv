// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Andreas Kurth  <akurth@iis.ee.ethz.ch>

/// A synthesis test bench which instantiates various adapter variants.
module synth_bench (
  input logic clk_i,
  input logic rst_ni
);

  localparam int AXI_ADDR_WIDTH[6] = {32, 64, 1, 2, 42, 129};
  localparam int AXI_ID_USER_WIDTH[3] = {0, 1, 8};
  localparam int NUM_SLAVE_MASTER[3] = {1, 2, 4};

  // AXI_DATA_WIDTH = {8, 16, 32, 64, 128, 256, 512, 1024}
  for (genvar i = 0; i < 8; i++) begin
    localparam DW = (2**i) * 8;
    synth_slice #(.AW(32), .DW(DW), .IW(8), .UW(8)) s(.*);
  end

  // AXI_ADDR_WIDTH
  for (genvar i = 0; i < 6; i++) begin
    localparam int AW = AXI_ADDR_WIDTH[i];
    synth_slice #(.AW(AW), .DW(32), .IW(8), .UW(8)) s(.*);
  end

  // AXI_ID_WIDTH and AXI_USER_WIDTH
  for (genvar i = 0; i < 3; i++) begin
    localparam int UW = AXI_ID_USER_WIDTH[i];
    localparam int IW = (UW == 0) ? 1 : UW;
    synth_slice #(.AW(32), .DW(32), .IW(IW), .UW(UW)) s(.*);
  end

  // ATOP Filter
  for (genvar iID = 1; iID <= 8; iID++) begin
    localparam int IW = iID;
    for (genvar iTxn = 1; iTxn <= 12; iTxn++) begin
      localparam int WT = iTxn;
      synth_axi_atop_filter #(
        .AXI_ADDR_WIDTH     (64),
        .AXI_DATA_WIDTH     (64),
        .AXI_ID_WIDTH       (IW),
        .AXI_USER_WIDTH     (4),
        .AXI_MAX_WRITE_TXNS (WT)
      ) i_filter (.*);
    end
  end

  // AXI4-Lite crossbar
  for (genvar i = 0; i < 3; i++) begin
    synth_axi_lite_xbar #(
      .NoSlvMst  ( NUM_SLAVE_MASTER[i] )
    ) i_lite_xbar (.*);
  end

  // Clock Domain Crossing
  for (genvar i = 0; i < 6; i++) begin
    localparam int AW = AXI_ADDR_WIDTH[i];
    for (genvar j = 0; j < 3; j++) begin
      localparam IUW = AXI_ID_USER_WIDTH[j];
      synth_axi_cdc #(
        .AXI_ADDR_WIDTH (AW),
        .AXI_DATA_WIDTH (128),
        .AXI_ID_WIDTH   (IUW),
        .AXI_USER_WIDTH (IUW)
      ) i_cdc (.*);
    end
  end

  // AXI4-Lite to APB bridge
  for (genvar i_data = 0; i_data < 3; i_data++) begin
    localparam int unsigned DataWidth = (2**i_data) * 8;
    for (genvar i_slv = 0; i_slv < 3; i_slv++) begin
      synth_axi_lite_to_apb #(
        .NoApbSlaves ( NUM_SLAVE_MASTER[i_slv] ),
        .DataWidth   ( DataWidth               )
      ) i_axi_lite_to_apb (.*);
    end
  end

  // AXI4-Lite Mailbox
  for (genvar i_irq_mode = 0; i_irq_mode < 4; i_irq_mode++) begin
    localparam bit EDGE_TRIG = i_irq_mode[0];
    localparam bit ACT_HIGH  = i_irq_mode[1];
    for (genvar i_depth = 2; i_depth < 8; i_depth++) begin
      localparam int unsigned DEPTH = 2**i_depth;
      synth_axi_lite_mailbox #(
        .MAILBOX_DEPTH ( DEPTH     ),
        .IRQ_EDGE_TRIG ( EDGE_TRIG ),
        .IRQ_ACT_HIGH  ( ACT_HIGH  )
      ) i_axi_lite_mailbox (.*);
    end
  end
endmodule


module synth_slice #(
  parameter int AW = -1,
  parameter int DW = -1,
  parameter int IW = -1,
  parameter int UW = -1
)(
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) a_full(), b_full();

  AXI_LITE #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) a_lite(), b_lite();

  axi_to_axi_lite_intf #(
    .AXI_ID_WIDTH       (IW),
    .AXI_ADDR_WIDTH     (AW),
    .AXI_DATA_WIDTH     (DW),
    .AXI_USER_WIDTH     (UW),
    .AXI_MAX_WRITE_TXNS (32'd10),
    .AXI_MAX_READ_TXNS  (32'd10),
    .FALL_THROUGH       (1'b0)
  ) a (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .testmode_i (1'b0),
    .slv        (a_full.Slave),
    .mst        (a_lite.Master)
  );
  axi_lite_to_axi_intf b (
    .in   (b_lite.Slave),
    .out  (b_full.Master)
  );

endmodule


module synth_axi_atop_filter #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0
) (
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();

  axi_atop_filter_intf #(
    .AXI_ID_WIDTH       (AXI_ID_WIDTH),
    .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS)
  ) dut (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .slv    (upstream),
    .mst    (downstream)
  );
endmodule

`include "axi/typedef.svh"

module synth_axi_lite_to_apb #(
  parameter int unsigned NoApbSlaves = 0,
  parameter int unsigned DataWidth   = 0
) (
  input logic clk_i,  // Clock
  input logic rst_ni  // Asynchronous reset active low
);

  typedef logic [31:0]            addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [DataWidth/8-1:0] strb_t;

  typedef struct packed {
    addr_t          paddr;   // same as AXI4-Lite
    axi_pkg::prot_t pprot;   // same as AXI4-Lite, specification is the same
    logic           psel;    // one request line per connected APB4 slave
    logic           penable; // enable signal shows second APB4 cycle
    logic           pwrite;  // write enable
    data_t          pwdata;  // write data, comes from W channel
    strb_t          pstrb;   // write strb, comes from W channel
  } apb_req_t;

  typedef struct packed {
    logic  pready;   // slave signals that it is ready
    data_t prdata;   // read data, connects to R channel
    logic  pslverr;  // gets translated into either `axi_pkg::RESP_OK` or `axi_pkg::RESP_SLVERR`
  } apb_resp_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T (  aw_chan_t, addr_t         )
  `AXI_LITE_TYPEDEF_W_CHAN_T  (   w_chan_t, data_t, strb_t )
  `AXI_LITE_TYPEDEF_B_CHAN_T  (   b_chan_t                 )
  `AXI_LITE_TYPEDEF_AR_CHAN_T (  ar_chan_t, addr_t         )
  `AXI_LITE_TYPEDEF_R_CHAN_T  (   r_chan_t, data_t         )
  `AXI_LITE_TYPEDEF_REQ_T     (  axi_req_t, aw_chan_t, w_chan_t, ar_chan_t )
  `AXI_LITE_TYPEDEF_RESP_T    ( axi_resp_t,  b_chan_t, r_chan_t )

  axi_req_t                    axi_req;
  axi_resp_t                   axi_resp;
  apb_req_t  [NoApbSlaves-1:0] apb_req;
  apb_resp_t [NoApbSlaves-1:0] apb_resp;

  axi_pkg::xbar_rule_32_t [NoApbSlaves-1:0] addr_map;

  axi_lite_to_apb #(
    .NoApbSlaves     ( NoApbSlaves             ),
    .NoRules         ( NoApbSlaves             ),
    .AddrWidth       ( 32'd32                  ),
    .DataWidth       ( DataWidth               ),
    .axi_lite_req_t  ( axi_req_t               ),
    .axi_lite_resp_t ( axi_resp_t              ),
    .apb_req_t       ( apb_req_t               ),
    .apb_resp_t      ( apb_resp_t              ),
    .rule_t          ( axi_pkg::xbar_rule_32_t )
  ) i_axi_lite_to_apb_dut (
    .clk_i           ( clk_i    ),
    .rst_ni          ( rst_ni   ),
    .axi_lite_req_i  ( axi_req  ),
    .axi_lite_resp_o ( axi_resp ),
    .apb_req_o       ( apb_req  ),
    .apb_resp_i      ( apb_resp ),
    .addr_map_i      ( addr_map )
  );

endmodule

module synth_axi_cdc #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0
) (
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();

  axi_cdc_intf #(
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH),
    .LOG_DEPTH      (2)
  ) dut (
    .src_clk_i  (clk_i),
    .src_rst_ni (rst_ni),
    .src        (upstream),
    .dst_clk_i  (clk_i),
    .dst_rst_ni (rst_ni),
    .dst        (downstream)
  );

endmodule

`include "axi/typedef.svh"

module synth_axi_lite_xbar #(
  parameter int unsigned NoSlvMst = 32'd1
) (
  input logic clk_i,  // Clock
  input logic rst_ni  // Asynchronous reset active low
);
  typedef logic [32'd32-1:0]   addr_t;
  typedef logic [32'd32-1:0]   data_t;
  typedef logic [32'd32/8-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T ( aw_chan_t, addr_t        )
  `AXI_LITE_TYPEDEF_W_CHAN_T  (  w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T  (  b_chan_t                )
  `AXI_LITE_TYPEDEF_AR_CHAN_T ( ar_chan_t, addr_t        )
  `AXI_LITE_TYPEDEF_R_CHAN_T  (  r_chan_t, data_t        )
  `AXI_LITE_TYPEDEF_REQ_T     (     req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T    (    resp_t,  b_chan_t, r_chan_t)
  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:         NoSlvMst,
    NoMstPorts:         NoSlvMst,
    MaxMstTrans:        32'd5,
    MaxSlvTrans:        32'd5,
    FallThrough:        1'b1,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    AxiAddrWidth:       32'd32,
    AxiDataWidth:       32'd32,
    NoAddrRules:        NoSlvMst,
    default:            '0
  };

  axi_pkg::xbar_rule_32_t [NoSlvMst-1:0] addr_map;
  logic                                  test;
  req_t                   [NoSlvMst-1:0] mst_reqs,  slv_reqs;
  resp_t                  [NoSlvMst-1:0] mst_resps, slv_resps;

  axi_lite_xbar #(
    .Cfg       ( XbarCfg                 ),
    .aw_chan_t ( aw_chan_t               ),
    .w_chan_t  (  w_chan_t               ),
    .b_chan_t  (  b_chan_t               ),
    .ar_chan_t ( ar_chan_t               ),
    .r_chan_t  (  r_chan_t               ),
    .req_t     (     req_t               ),
    .resp_t    (    resp_t               ),
    .rule_t    ( axi_pkg::xbar_rule_32_t )
  ) i_xbar_dut (
    .clk_i                 ( clk_i     ),
    .rst_ni                ( rst_ni    ),
    .test_i                ( test      ),
    .slv_ports_req_i       ( mst_reqs  ),
    .slv_ports_resp_o      ( mst_resps ),
    .mst_ports_req_o       ( slv_reqs  ),
    .mst_ports_resp_i      ( slv_resps ),
    .addr_map_i            ( addr_map  ),
    .en_default_mst_port_i ( '0        ),
    .default_mst_port_i    ( '0        )
  );
endmodule

module synth_axi_lite_mailbox #(
  parameter int unsigned MAILBOX_DEPTH = 32'd1,
  parameter bit          IRQ_EDGE_TRIG = 1'b0,
  parameter bit          IRQ_ACT_HIGH  = 1'b0
) (
  input logic clk_i,  // Clock
  input logic rst_ni  // Asynchronous reset active low
);
  typedef logic [32'd32-1:0]   addr_t;

  AXI_LITE #(
    .AXI_ADDR_WIDTH (32'd32),
    .AXI_DATA_WIDTH (32'd32)
  ) slv [1:0] ();

  logic        test;
  logic  [1:0] irq;
  addr_t [1:0] base_addr;

  axi_lite_mailbox_intf #(
    .MAILBOX_DEPTH  ( MAILBOX_DEPTH  ),
    .IRQ_EDGE_TRIG  ( IRQ_EDGE_TRIG  ),
    .IRQ_ACT_HIGH   ( IRQ_ACT_HIGH   ),
    .AXI_ADDR_WIDTH ( 32'd32         ),
    .AXI_DATA_WIDTH ( 32'd32         )
  ) i_axi_lite_mailbox (
    .clk_i       ( clk_i     ), // Clock
    .rst_ni      ( rst_ni    ), // Asynchronous reset active low
    .test_i      ( test      ), // Testmode enable
    // slave ports [1:0]
    .slv         ( slv       ),
    .irq_o       ( irq       ), // interrupt output for each port
    .base_addr_i ( base_addr )  // base address for each port
  );
endmodule
