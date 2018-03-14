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
// Author: Florian Zaruba, ETH Zurich
// Date: 19.03.2017
// Description: Ariane Top-level module

import ariane_pkg::*;
`default_nettype none

module ariane_nexys4ddr
  (
   // DDR2 RAM
   inout wire [15:0]  ddr_dq,
   inout wire [1:0]   ddr_dqs_n,
   inout wire [1:0]   ddr_dqs_p,
   output wire [12:0] ddr_addr,
   output wire [2:0]  ddr_ba,
   output wire        ddr_ras_n,
   output wire        ddr_cas_n,
   output wire        ddr_we_n,
   output wire        ddr_ck_n,
   output wire        ddr_ck_p,
   output wire        ddr_cke,
   output wire        ddr_cs_n,
   output wire [1:0]  ddr_dm,
   output wire        ddr_odt,
   input  wire        rxd,
   output wire        txd,
   output wire        rts,
   input  wire        cts,
   // 4-bit full SD interface
   output wire        sd_sclk,
   input wire         sd_detect,
   inout wire [3:0]   sd_dat,
   inout wire         sd_cmd,
   output wire        sd_reset,

   // LED and DIP switch
   output wire [7:0]  o_led,
   input wire [15:0]  i_dip,

   // push button array
   input wire         GPIO_SW_C,
   input wire         GPIO_SW_W,
   input wire         GPIO_SW_E,
   input wire         GPIO_SW_N,
   input wire         GPIO_SW_S,

   //keyboard
   inout wire         PS2_CLK,
   inout wire         PS2_DATA,

  // display
   output wire        VGA_HS_O,
   output wire        VGA_VS_O,
   output wire [3:0]  VGA_RED_O,
   output wire [3:0]  VGA_BLUE_O,
   output wire [3:0]  VGA_GREEN_O,

   // Ethernet
 input wire [1:0]   i_erxd, // RMII receive data
 input wire         i_erx_dv, // PHY data valid
 input wire         i_erx_er, // PHY coding error
 input wire         i_emdint, // PHY interrupt in active low
 output reg         o_erefclk, // RMII clock out
 output reg [1:0]   o_etxd, // RMII transmit data
 output reg         o_etx_en, // RMII transmit enable
 output wire        o_emdc, // MDIO clock
 inout wire         io_emdio, // MDIO inout
 output wire        o_erstn, // PHY reset active low

  // JTAG signals
    input  logic     tck_i,
    input  logic     trstn_i,
    input  logic     tms_i,
    input  logic     tdi_i,
    output logic     tdo_o,

   // clock and reset
   input wire        clk_p,
   input wire        clk_n,
   input wire        rst_top
   );

   logic             clk_i, locked, tdo;          
   logic             test_en_i = 'b1; // enable all clock gates for testing
   // Core ID; Cluster ID and boot address are considered more or less static
   logic [ 3:0]      core_id_i = 'b0;
   logic [ 5:0]      cluster_id_i = 'b0;
   logic             flush_req_i = 'b0;
   logic             flushing_o;
   // Interrupt s
   logic [1:0]       irq_i = 'b0; // level sensitive IR lines; mip & sip
   logic             ipi_i = 'b0; // inter-processor interrupts
   logic             sec_lvl_o; // current privilege level oot
   // Timer facilities
   logic [63:0]      time_i = 'b0; // global time (most probably coming from an RTC)
   logic             time_irq_i = 'b0; // timer interrupt in

   parameter logic [63:0]               CACHE_START_ADDR  = 64'h8000_0000;
 // address on which to decide whether the request is cache-able or not
   parameter int                        unsigned AXI_ID_WIDTH      = 4;
   parameter int                        unsigned AXI_USER_WIDTH    = 1;
   parameter int                        unsigned AXI_ADDRESS_WIDTH = 64;
   parameter int                        unsigned AXI_DATA_WIDTH    = 64;
   
   genvar        i;

   // internal clock and reset signals
   logic  rst, rst_ni;
   assign rst = !rst_ni;

   // Debug controlled reset of the Rocket system
   logic  sys_rst, cpu_rst;

   // interrupt line
   logic [63:0]                interrupt;

wire io_emdio_i, phy_emdio_o, phy_emdio_t, clk_rmii, clk_rmii_quad, clk_locked, clk_locked_wiz, aresetn;
reg phy_emdio_i, io_emdio_o, io_emdio_t;

   // the NASTI bus for off-FPGA DRAM, converted to High frequency
   nasti_channel   
     #(
       .ID_WIDTH    ( 10 ),
       .ADDR_WIDTH  ( 32 ),
       .DATA_WIDTH  ( 64 ))
   mem_mig_nasti();

   // MIG clock
   logic mig_ui_clk, mig_ui_rst, mig_ui_rstn;
   logic mig_sys_clk, clk_pixel;
   logic clk_io_uart; // UART IO clock for debug
   assign mig_ui_rstn = !mig_ui_rst;

    logic        master0_req,     master1_req,     master2_req,     master3_req;
    logic [63:0] master0_address, master1_address, master2_address, master3_address;
    logic [7:0]  master0_we,      master1_we,      master2_we,      master3_we;
    logic [63:0] master0_wdata,   master1_wdata,   master2_wdata,   master3_wdata;
    logic [63:0] master0_rdata,   master1_rdata,   master2_rdata,   master3_rdata;

    AXI_BUS #(
              .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
              .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
              .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
              .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) instr_if(), data_if(), bypass_if(), input_if(), output_if(), master0_if(), master1_if(), master2_if(), master3_if();

`ifdef MIG
   
   // clock converter
   axi_clock_converter_0 clk_conv
     (
      .s_axi_aclk           ( clk_i                    ),
      .s_axi_aresetn        ( aresetn                  ),
  .s_axi_awid(master2_if.aw_id),
  .s_axi_awaddr(master2_if.aw_addr),
  .s_axi_awlen(master2_if.aw_len),
  .s_axi_awsize(master2_if.aw_size),
  .s_axi_awburst(master2_if.aw_burst),
  .s_axi_awlock(master2_if.aw_lock),
  .s_axi_awcache(master2_if.aw_cache),
  .s_axi_awprot(master2_if.aw_prot),
  .s_axi_awregion(master2_if.aw_region),
  .s_axi_awqos(master2_if.aw_qos),
  .s_axi_awuser(master2_if.aw_user),
  .s_axi_awvalid(master2_if.aw_valid),
  .s_axi_awready(master2_if.aw_ready),
  .s_axi_wdata(master2_if.w_data),
  .s_axi_wstrb(master2_if.w_strb),
  .s_axi_wlast(master2_if.w_last),
  .s_axi_wuser(master2_if.w_user),
  .s_axi_wvalid(master2_if.w_valid),
  .s_axi_wready(master2_if.w_ready),
  .s_axi_bid(master2_if.b_id),
  .s_axi_bresp(master2_if.b_resp),
  .s_axi_buser(master2_if.b_user),
  .s_axi_bvalid(master2_if.b_valid),
  .s_axi_bready(master2_if.b_ready),
  .s_axi_arid(master2_if.ar_id),
  .s_axi_araddr(master2_if.ar_addr),
  .s_axi_arlen(master2_if.ar_len),
  .s_axi_arsize(master2_if.ar_size),
  .s_axi_arburst(master2_if.ar_burst),
  .s_axi_arlock(master2_if.ar_lock),
  .s_axi_arcache(master2_if.ar_cache),
  .s_axi_arprot(master2_if.ar_prot),
  .s_axi_arregion(master2_if.ar_region),
  .s_axi_arqos(master2_if.ar_qos),
  .s_axi_aruser(master2_if.ar_user),
  .s_axi_arvalid(master2_if.ar_valid),
  .s_axi_arready(master2_if.ar_ready),
  .s_axi_rid(master2_if.r_id),
  .s_axi_rdata(master2_if.r_data),
  .s_axi_rresp(master2_if.r_resp),
  .s_axi_rlast(master2_if.r_last),
  .s_axi_ruser(master2_if.r_user),
  .s_axi_rvalid(master2_if.r_valid),
  .s_axi_rready(master2_if.r_ready),
      .m_axi_aclk           ( mig_ui_clk               ),
      .m_axi_aresetn        ( aresetn                  ),
      .m_axi_awid           ( mem_mig_nasti.aw_id      ),
      .m_axi_awaddr         ( mem_mig_nasti.aw_addr    ),
      .m_axi_awlen          ( mem_mig_nasti.aw_len     ),
      .m_axi_awsize         ( mem_mig_nasti.aw_size    ),
      .m_axi_awburst        ( mem_mig_nasti.aw_burst   ),
      .m_axi_awlock         (                          ), // not supported in AXI4
      .m_axi_awcache        ( mem_mig_nasti.aw_cache   ),
      .m_axi_awprot         ( mem_mig_nasti.aw_prot    ),
      .m_axi_awqos          ( mem_mig_nasti.aw_qos     ),
      .m_axi_awregion       ( mem_mig_nasti.aw_region  ),
      .m_axi_awvalid        ( mem_mig_nasti.aw_valid   ),
      .m_axi_awready        ( mem_mig_nasti.aw_ready   ),
      .m_axi_awuser         ( mem_mig_nasti.aw_user    ),
      .m_axi_wdata          ( mem_mig_nasti.w_data     ),
      .m_axi_wstrb          ( mem_mig_nasti.w_strb     ),
      .m_axi_wlast          ( mem_mig_nasti.w_last     ),
      .m_axi_wvalid         ( mem_mig_nasti.w_valid    ),
      .m_axi_wready         ( mem_mig_nasti.w_ready    ),
      .m_axi_wuser          ( mem_mig_nasti.w_user     ),
      .m_axi_bid            ( mem_mig_nasti.b_id       ),
      .m_axi_bresp          ( mem_mig_nasti.b_resp     ),
      .m_axi_bvalid         ( mem_mig_nasti.b_valid    ),
      .m_axi_bready         ( mem_mig_nasti.b_ready    ),
      .m_axi_buser          ( mem_mig_nasti.b_user     ),
      .m_axi_arid           ( mem_mig_nasti.ar_id      ),
      .m_axi_araddr         ( mem_mig_nasti.ar_addr    ),
      .m_axi_arlen          ( mem_mig_nasti.ar_len     ),
      .m_axi_arsize         ( mem_mig_nasti.ar_size    ),
      .m_axi_arburst        ( mem_mig_nasti.ar_burst   ),
      .m_axi_arlock         (                          ), 
      .m_axi_arcache        ( mem_mig_nasti.ar_cache   ),
      .m_axi_arprot         ( mem_mig_nasti.ar_prot    ),
      .m_axi_arqos          ( mem_mig_nasti.ar_qos     ),
      .m_axi_arregion       ( mem_mig_nasti.ar_region  ),
      .m_axi_arvalid        ( mem_mig_nasti.ar_valid   ),
      .m_axi_arready        ( mem_mig_nasti.ar_ready   ),
      .m_axi_aruser         ( mem_mig_nasti.ar_user    ),
      .m_axi_rid            ( mem_mig_nasti.r_id       ),
      .m_axi_rdata          ( mem_mig_nasti.r_data     ),
      .m_axi_rresp          ( mem_mig_nasti.r_resp     ),
      .m_axi_rlast          ( mem_mig_nasti.r_last     ),
      .m_axi_rvalid         ( mem_mig_nasti.r_valid    ),
      .m_axi_rready         ( mem_mig_nasti.r_ready    ),
      .m_axi_ruser          ( mem_mig_nasti.r_user     )
    );

assign mem_mig_nasti.b_user = 'b0; // not supported in AXI4
assign mem_mig_nasti.r_user = 'b0;

   clk_wiz_ariane clk_gen
     (
      .clk_in1       ( clk_p         ), // 100 MHz onboard
      .clk_out1      ( mig_sys_clk   ), // 200 MHz
      .clk_io_uart   ( clk_io_uart   ), // 60 MHz
      .clk_rmii      ( clk_rmii      ), // 50 MHz rmii
      .clk_rmii_quad ( clk_rmii_quad ), // 50 MHz rmii quad
      .clk_pixel     ( clk_pixel     ), // 120 MHz
      .clk_i         (               ), // 25 MHz (only if DDR not used)
      .resetn        ( rst_top       ),
      .locked        ( clk_locked_wiz )
      );
   
   // DRAM controller
   mig_7series_0 dram_ctl
     (
      .sys_clk_i            ( mig_sys_clk            ),
      .sys_rst              ( clk_locked             ),
      .ui_addn_clk_0        ( clk_i                  ),
      .ui_addn_clk_1        (                        ),
      .ui_addn_clk_2        (                        ),
      .ui_addn_clk_3        (                        ),
      .ui_addn_clk_4        (                        ),
      .device_temp_i        ( 12'b0                  ),
      .ddr2_dq              ( ddr_dq                 ),
      .ddr2_dqs_n           ( ddr_dqs_n              ),
      .ddr2_dqs_p           ( ddr_dqs_p              ),
      .ddr2_addr            ( ddr_addr               ),
      .ddr2_ba              ( ddr_ba                 ),
      .ddr2_ras_n           ( ddr_ras_n              ),
      .ddr2_cas_n           ( ddr_cas_n              ),
      .ddr2_we_n            ( ddr_we_n               ),
      .ddr2_ck_p            ( ddr_ck_p               ),
      .ddr2_ck_n            ( ddr_ck_n               ),
      .ddr2_cke             ( ddr_cke                ),
      .ddr2_cs_n            ( ddr_cs_n               ),
      .ddr2_dm              ( ddr_dm                 ),
      .ddr2_odt             ( ddr_odt                ),
      .ui_clk               ( mig_ui_clk             ),
      .ui_clk_sync_rst      ( mig_ui_rst             ),
      .mmcm_locked          ( rst_ni                 ),
      .aresetn              ( aresetn                ), // AXI reset
      .app_sr_req           ( 1'b0                   ),
      .app_sr_active        (                        ),
      .app_ref_req          ( 1'b0                   ),
      .app_ref_ack          (                        ),
      .app_zq_req           ( 1'b0                   ),
      .app_zq_ack           (                        ),
      .init_calib_complete  (                        ),
      .s_axi_awid           ( mem_mig_nasti.aw_id    ),
      .s_axi_awaddr         ( mem_mig_nasti.aw_addr  ),
      .s_axi_awlen          ( mem_mig_nasti.aw_len   ),
      .s_axi_awsize         ( mem_mig_nasti.aw_size  ),
      .s_axi_awburst        ( mem_mig_nasti.aw_burst ),
      .s_axi_awlock         ( 1'b0                   ), // not supported in AXI4
      .s_axi_awcache        ( mem_mig_nasti.aw_cache ),
      .s_axi_awprot         ( mem_mig_nasti.aw_prot  ),
      .s_axi_awqos          ( mem_mig_nasti.aw_qos   ),
      .s_axi_awvalid        ( mem_mig_nasti.aw_valid ),
      .s_axi_awready        ( mem_mig_nasti.aw_ready ),
      .s_axi_wdata          ( mem_mig_nasti.w_data   ),
      .s_axi_wstrb          ( mem_mig_nasti.w_strb   ),
      .s_axi_wlast          ( mem_mig_nasti.w_last   ),
      .s_axi_wvalid         ( mem_mig_nasti.w_valid  ),
      .s_axi_wready         ( mem_mig_nasti.w_ready  ),
      .s_axi_bid            ( mem_mig_nasti.b_id     ),
      .s_axi_bresp          ( mem_mig_nasti.b_resp   ),
      .s_axi_bvalid         ( mem_mig_nasti.b_valid  ),
      .s_axi_bready         ( mem_mig_nasti.b_ready  ),
      .s_axi_arid           ( mem_mig_nasti.ar_id    ),
      .s_axi_araddr         ( mem_mig_nasti.ar_addr  ),
      .s_axi_arlen          ( mem_mig_nasti.ar_len   ),
      .s_axi_arsize         ( mem_mig_nasti.ar_size  ),
      .s_axi_arburst        ( mem_mig_nasti.ar_burst ),
      .s_axi_arlock         ( 1'b0                   ), // not supported in AXI4
      .s_axi_arcache        ( mem_mig_nasti.ar_cache ),
      .s_axi_arprot         ( mem_mig_nasti.ar_prot  ),
      .s_axi_arqos          ( mem_mig_nasti.ar_qos   ),
      .s_axi_arvalid        ( mem_mig_nasti.ar_valid ),
      .s_axi_arready        ( mem_mig_nasti.ar_ready ),
      .s_axi_rid            ( mem_mig_nasti.r_id     ),
      .s_axi_rdata          ( mem_mig_nasti.r_data   ),
      .s_axi_rresp          ( mem_mig_nasti.r_resp   ),
      .s_axi_rlast          ( mem_mig_nasti.r_last   ),
      .s_axi_rvalid         ( mem_mig_nasti.r_valid  ),
      .s_axi_rready         ( mem_mig_nasti.r_ready  )
      );

`else // !`ifdef MIG

   assign mig_sys_clk   = clk_p;
   assign clk_io_uart   = clk_p;
   assign clk_rmii      = clk_p;
   assign clk_rmii_quad = clk_p;
   assign clk_pixel     = clk_p;
   assign clk_locked_wiz= rst_top;
   assign clk_i         = clk_p;
   assign rst_ni        = rst_top;

axi_ram_wrap_ariane  #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    ),
        .MEM_ADDR_WIDTH ( 30                )
    ) i_master_behav (
        .clk_i  ( clk_i           ),
        .rst_ni ( aresetn         ),
        .slave  ( master2_if      ),
        .bram_en_a  ( master2_req     ),
        .bram_addr_a ( master2_address ),
        .bram_we_a   ( master2_we      ),
        .bram_wrdata_a ( master2_wdata   ),
        .bram_rddata_a ( master2_rdata   ),
        .bram_clk_a ( ),
        .bram_rst_a ( ));

infer_ram  #(
        .RAM_SIZE(24),
        .BYTE_WIDTH(8))
        my_master2_behav (
      .ram_clk(clk_i),    // input wire clka
      .ram_en(master2_req),      // input wire ena
      .ram_we(master2_we),   // input wire [7 : 0] wea
      .ram_addr(master2_address[26:3]),  // input wire [13: 0] addra
      .ram_wrdata(master2_wdata),  // input wire [63 : 0] dina
      .ram_rddata(master2_rdata)  // output wire [63 : 0] douta
      );
                      
`endif

   assign clk_locked = &{clk_locked_wiz, rst_top};
   
   /////////////////////////////////////////////////////////////
   // HID

   logic                       hid_irq, sd_irq, eth_irq;

   wire                        hid_rst, hid_clk, hid_en;
   wire [7:0]                  hid_we;
   wire [17:0]                 hid_addr;
   wire [63:0]                 hid_wrdata,  hid_rddata;
   logic [30:0]                hid_ar_addr, hid_aw_addr;
   logic [1:0] eth_txd;
   logic eth_rstn, eth_refclk, eth_txen;
   assign o_erstn = eth_rstn & clk_locked_wiz;
    
   always @(posedge clk_rmii)
     begin
        phy_emdio_i <= io_emdio_i;
        io_emdio_o <= phy_emdio_o;
        io_emdio_t <= phy_emdio_t;
     end

   IOBUF #(
      .DRIVE(12), // Specify the output drive strength
      .IBUF_LOW_PWR("TRUE"),  // Low Power - "TRUE", High Performance = "FALSE" 
      .IOSTANDARD("DEFAULT"), // Specify the I/O standard
      .SLEW("SLOW") // Specify the output slew rate
   ) IOBUF_inst (
      .O(io_emdio_i),     // Buffer output
      .IO(io_emdio),   // Buffer inout port (connect directly to top-level port)
      .I(io_emdio_o),     // Buffer input
      .T(io_emdio_t)      // 3-state enable input, high=input, low=output
   );

  ODDR #(
    .DDR_CLK_EDGE("OPPOSITE_EDGE"),
    .INIT(1'b0),
    .IS_C_INVERTED(1'b0),
    .IS_D1_INVERTED(1'b0),
    .IS_D2_INVERTED(1'b0),
    .SRTYPE("SYNC")) 
    refclk_inst
       (.C(eth_refclk),
        .CE(1'b1),
        .D1(1'b1),
        .D2(1'b0),
        .Q(o_erefclk),
        .R(1'b0),
        .S( ));
    
    always @(posedge clk_rmii_quad)
        begin
        o_etxd = eth_txd;
        o_etx_en = eth_txen;
        end

   periph_soc psoc
     (
      .msoc_clk   ( clk_i           ),
      .sd_sclk    ( sd_sclk         ),
      .sd_detect  ( sd_detect       ),
      .sd_dat     ( sd_dat          ),
      .sd_cmd     ( sd_cmd          ),
      .sd_irq     ( sd_irq          ),
      .from_dip   ( i_dip           ),
      .to_led     ( o_led           ),
      .rstn       ( clk_locked      ),
      .clk_200MHz ( mig_sys_clk     ),
      .pxl_clk    ( clk_pixel       ),
      .uart_rx    ( rxd             ),
      .uart_tx    ( txd             ),
      .clk_rmii   ( clk_rmii        ),
      .locked     ( clk_locked      ),
    // SMSC ethernet PHY connections
      .eth_rstn   ( eth_rstn        ),
      .eth_crsdv  ( i_erx_dv        ),
      .eth_refclk ( eth_refclk      ),
      .eth_txd    ( eth_txd         ),
      .eth_txen   ( eth_txen        ),
      .eth_rxd    ( i_erxd          ),
      .eth_rxerr  ( i_erx_er        ),
      .eth_mdc    ( o_emdc          ),
      .phy_mdio_i ( phy_emdio_i     ),
      .phy_mdio_o ( phy_emdio_o     ),
      .phy_mdio_t ( phy_emdio_t     ),
      .eth_irq    ( eth_irq         ),
      .*
      );

    localparam int unsigned AXI_NUMBYTES = AXI_DATA_WIDTH/8;

    logic        flush_dcache_ack, flush_dcache;
    logic        flush_dcache_q;
    logic [31:0] dbg_mstaddress;
    
    ariane #(
        .CACHE_START_ADDR ( CACHE_START_ADDR ),
        .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH   ( AXI_USER_WIDTH   )
    ) i_ariane (
        .*,
        .rst_ni                 ( aresetn              ),
        .flush_dcache_i         ( flush_dcache         ),
        .flush_dcache_ack_o     ( flush_dcache_ack     ),
        .data_if                ( data_if              ),
        .bypass_if              ( bypass_if            ),
        .instr_if               ( instr_if             ),
        .boot_addr_i            ( 64'h40000000         )
        );

    assign flush_dcache = flush_dcache_q;
    assign flushing_o = flush_dcache_q;
    
    // direct store interface
    always_ff @(posedge clk_i or negedge rst_ni) begin

        if (~rst_ni) begin
            flush_dcache_q  <= 1'b0;
        end else begin
            // got acknowledge from dcache - release the flush signal
            if (flush_dcache_ack)
                flush_dcache_q <= 1'b0;

            if (flush_req_i) begin
                flush_dcache_q <= 1'b1;
            end
        end
    end

        // Debug Interface
   logic                                 debug_gnt_o;
   logic                                 debug_halt_i;
   logic                                 debug_resume_i;
   logic                                 debug_rvalid_o;
   logic [15:0]                          debug_addr_i;
   logic                                 debug_we_i;
   logic [63:0]                          debug_wdata_i;
   logic [63:0]                          debug_rdata_o;
   logic                                 debug_halted_o;
   logic                                 debug_req_i;
         
   // CPU Control Signals
   logic                                 fetch_enable_i;
 
   crossbar_socip cross1(
      .slave0_if  ( instr_if   ),
      .slave1_if  ( data_if    ),
      .slave2_if  ( bypass_if  ),
      .slave3_if  ( input_if   ),
      .slave4_if  ( output_if  ),
      .master0_if ( master0_if ),
      .master1_if ( master1_if ),
      .master2_if ( master2_if ),
      .master3_if ( master3_if ),
      .clk_i      ( clk_i      ),
      .rst_ni     ( aresetn    ));

   dbg_wrap #(
      .JTAG_CHAIN_START     ( 1                 ),
      .AXI_ID_MASTER_WIDTH  ( AXI_ID_WIDTH      ),
      .AXI_ID_SLAVE_WIDTH   ( AXI_ID_WIDTH      ),
      .AXI_ADDR_WIDTH       ( AXI_ADDRESS_WIDTH ),
      .AXI_DATA_WIDTH       ( AXI_DATA_WIDTH    ),
      .AXI_USER_WIDTH       ( AXI_USER_WIDTH    )
    ) i_dbg (
        .clk        ( clk_i          ),
        .rst_n      ( rst_ni         ),
        .testmode_i ( 1'b0           ),
        .input_if   ( input_if       ),
        .output_if  ( output_if      ),
        // CPU signals
        .aresetn      ( aresetn        ),
        .cpu_addr_o   ( debug_addr_i   ), 
        .cpu_rdata_i  ( debug_rdata_o  ),
        .cpu_wdata_o  ( debug_wdata_i  ),
        .cpu_halted_i ( debug_halted_o ),
        .cpu_halt_o   ( debug_halt_i   ),
        .cpu_resume_o ( debug_resume_i ),
        .cpu_req_o    ( debug_req_i    ),
        .cpu_we_o     ( debug_we_i     ),
        .cpu_rvalid_i ( debug_rvalid_o ),
        .cpu_gnt_i    ( debug_gnt_o    ),
        .cpu_fetch_o  ( fetch_enable_i ),
        // Boot memory at location 'h40000000
        .boot_en(master1_req),      // input wire ena
        .boot_we(master1_we),   // input wire [7 : 0] wea
        .boot_addr(master1_address[15:0]),  // input wire [13: 0] addra
        .boot_wdata(master1_wdata),  // input wire [63 : 0] dina
        .boot_rdata(master1_rdata),  // output wire [63 : 0] douta
        // JTAG shared memory at location 'h42000000
        .wrap_en(master3_req),      // input wire ena
        .wrap_we(master3_we),   // input wire [7 : 0] wea
        .wrap_addr(master3_address[13:0]),  // input wire [13: 0] addra
        .wrap_wdata(master3_wdata),  // input wire [63 : 0] dina
        .wrap_rdata(master3_rdata),  // output wire [63 : 0] douta
        .address      ( dbg_mstaddress ),
        .i_dip        ( i_dip          ),
        .tms_i        ( tms_i          ),
        .tck_i        ( tck_i          ),
        .trstn_i      ( rst_top        ),
        .tdi_i        ( tdi_i          ),
        .tdo_o        ( tdo            )
             );

axi_ram_wrap_ariane  #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    ),
        .MEM_ADDR_WIDTH ( 20                )
    ) i_master0 (
        .clk_i  ( clk_i           ),
        .rst_ni ( rst_ni          ),
        .slave  ( master0_if      ),
        .bram_en_a  ( master0_req     ),
        .bram_addr_a ( master0_address ),
        .bram_we_a   ( master0_we      ),
        .bram_wrdata_a ( master0_wdata   ),
        .bram_rddata_a ( master0_rdata   ),
        .bram_clk_a ( ),
        .bram_rst_a ( )
    ), i_master1 (
        .clk_i  ( clk_i           ),
        .rst_ni ( rst_ni          ),
        .slave  ( master1_if      ),
        .bram_en_a  ( master1_req     ),
        .bram_addr_a ( master1_address ),
        .bram_we_a   ( master1_we      ),
        .bram_wrdata_a ( master1_wdata   ),
        .bram_rddata_a ( master1_rdata   ),
        .bram_clk_a ( ),
        .bram_rst_a ( )
    ), i_master3 (
                .clk_i  ( clk_i           ),
                .rst_ni ( rst_ni          ),
                .slave  ( master3_if      ),
                .bram_en_a  ( master3_req     ),
                .bram_addr_a ( master3_address ),
                .bram_we_a   ( master3_we      ),
                .bram_wrdata_a ( master3_wdata   ),
                .bram_rddata_a ( master3_rdata   ),
                .bram_clk_a ( ),
                .bram_rst_a ( )
    );

   assign hid_we = master0_we;
   assign hid_wrdata = master0_wdata;
   assign master0_rdata = hid_rddata;
   assign hid_addr = master0_address[17:0];
   assign hid_clk = clk_i;
   assign hid_en = master0_req;
   assign hid_rst = ~rst_ni;

endmodule
