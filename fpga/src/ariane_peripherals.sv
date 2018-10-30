// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Xilinx Peripehrals
module ariane_peripherals #(
    parameter int AxiAddrWidth = -1,
    parameter int AxiDataWidth = -1,
    parameter bit InclSPI      = 0
) (
    input  logic       clk_i           , // Clock
    input  logic       rst_ni          , // Asynchronous reset active low
    AXI_BUS.in         plic            ,
    AXI_BUS.in         uart            ,
    AXI_BUS.in         spi             ,
    output logic [1:0] irq_o           ,
    // UART
    input  logic       rx_i            ,
    output logic       tx_o            ,
    // SPI
    output logic       spi_clk_o       ,
    output logic       spi_mosi        ,
    input  logic       spi_miso        ,
    output logic       spi_ss
);

    // ---------------
    // PLIC
    // ---------------
    logic [ariane_soc::NumSources-1:0] irq_sources;

    REG_BUS #(
        .ADDR_WIDTH ( AxiAddrWidth ),
        .DATA_WIDTH ( AxiDataWidth )
    ) reg_bus (clk_i);

    AXI_LITE #(
        .AXI_ADDR_WIDTH ( AxiAddrWidth ),
        .AXI_DATA_WIDTH ( AxiDataWidth )
    ) axi_lite_plic ();

    axi_to_axi_lite i_axi_to_axi_lite_eth (
      .clk_i,
      .rst_ni,
      .testmode_i ( 1'b0          ),
      .in         ( plic          ),
      .out        ( axi_lite_plic )
    );

    axi_lite_to_reg #(
        .ADDR_WIDTH ( AxiAddrWidth  ),
        .DATA_WIDTH ( AxiDataWidth  )
    ) i_axi_lite_to_reg (
        .clk_i,
        .rst_ni,
        .axi_i      ( axi_lite_plic ), // AXI Lite
        .reg_o      ( reg_bus       )
    );

    plic #(
        .ADDR_WIDTH         ( AxiAddrWidth           ),
        .DATA_WIDTH         ( AxiDataWidth           ),
        .ID_BITWIDTH        ( 3                      ), // TODO (zarubaf): Find propper width
        .PARAMETER_BITWIDTH ( 3                      ), // TODO (zarubaf): Find propper width
        .NUM_TARGETS        ( ariane_soc::NumTargets ),
        .NUM_SOURCES        ( ariane_soc::NumSources )
    ) i_plic (
        .clk_i              ( clk_i                  ),
        .rst_ni             ( rst_ni                 ),
        .irq_sources_i      ( irq_sources            ),
        .eip_targets_o      ( irq_o                  ),
        .external_bus_io    ( reg_bus                )
    );

    // ---------------
    // UART
    // ---------------
    logic         uart_penable;
    logic         uart_pwrite;
    logic [31:0]  uart_paddr;
    logic         uart_psel;
    logic [31:0]  uart_pwdata;
    logic [31:0]  uart_prdata;
    logic         uart_pready;
    logic         uart_pslverr;

    axi2apb_64_32 #(
        .AXI4_ADDRESS_WIDTH ( AxiAddrWidth        ),
        .AXI4_RDATA_WIDTH   ( AxiDataWidth        ),
        .AXI4_WDATA_WIDTH   ( AxiDataWidth        ),
        .AXI4_ID_WIDTH      ( $bits(uart.aw_id)   ),
        .AXI4_USER_WIDTH    ( $bits(uart.aw_user) ),
        .BUFF_DEPTH_SLAVE   ( 2                   ),
        .APB_ADDR_WIDTH     ( 32                  )
    ) i_axi2apb_64_32 (
        .ACLK      ( clk_i          ),
        .ARESETn   ( rst_ni         ),
        .test_en_i ( 1'b0           ),
        .AWID_i    ( uart.aw_id     ),
        .AWADDR_i  ( uart.aw_addr   ),
        .AWLEN_i   ( uart.aw_len    ),
        .AWSIZE_i  ( uart.aw_size   ),
        .AWBURST_i ( uart.aw_burst  ),
        .AWLOCK_i  ( uart.aw_lock   ),
        .AWCACHE_i ( uart.aw_cache  ),
        .AWPROT_i  ( uart.aw_prot   ),
        .AWREGION_i( uart.aw_region ),
        .AWUSER_i  ( uart.aw_user   ),
        .AWQOS_i   ( uart.aw_qos    ),
        .AWVALID_i ( uart.aw_valid  ),
        .AWREADY_o ( uart.aw_ready  ),
        .WDATA_i   ( uart.w_data    ),
        .WSTRB_i   ( uart.w_strb    ),
        .WLAST_i   ( uart.w_last    ),
        .WUSER_i   ( uart.w_user    ),
        .WVALID_i  ( uart.w_valid   ),
        .WREADY_o  ( uart.w_ready   ),
        .BID_o     ( uart.b_id      ),
        .BRESP_o   ( uart.b_resp    ),
        .BVALID_o  ( uart.b_valid   ),
        .BUSER_o   ( uart.b_user    ),
        .BREADY_i  ( uart.b_ready   ),
        .ARID_i    ( uart.ar_id     ),
        .ARADDR_i  ( uart.ar_addr   ),
        .ARLEN_i   ( uart.ar_len    ),
        .ARSIZE_i  ( uart.ar_size   ),
        .ARBURST_i ( uart.ar_burst  ),
        .ARLOCK_i  ( uart.ar_lock   ),
        .ARCACHE_i ( uart.ar_cache  ),
        .ARPROT_i  ( uart.ar_prot   ),
        .ARREGION_i( uart.ar_region ),
        .ARUSER_i  ( uart.ar_user   ),
        .ARQOS_i   ( uart.ar_qos    ),
        .ARVALID_i ( uart.ar_valid  ),
        .ARREADY_o ( uart.ar_ready  ),
        .RID_o     ( uart.r_id      ),
        .RDATA_o   ( uart.r_data    ),
        .RRESP_o   ( uart.r_resp    ),
        .RLAST_o   ( uart.r_last    ),
        .RUSER_o   ( uart.r_user    ),
        .RVALID_o  ( uart.r_valid   ),
        .RREADY_i  ( uart.r_ready   ),
        .PENABLE   ( uart_penable   ),
        .PWRITE    ( uart_pwrite    ),
        .PADDR     ( uart_paddr     ),
        .PSEL      ( uart_psel      ),
        .PWDATA    ( uart_pwdata    ),
        .PRDATA    ( uart_prdata    ),
        .PREADY    ( uart_pready    ),
        .PSLVERR   ( uart_pslverr   )
    );

    apb_uart i_apb_uart (
        .CLK     ( clk_i           ),
        .RSTN    ( rst_ni          ),
        .PSEL    ( uart_psel       ),
        .PENABLE ( uart_penable    ),
        .PWRITE  ( uart_pwrite     ),
        .PADDR   ( uart_paddr[4:2] ),
        .PWDATA  ( uart_pwdata     ),
        .PRDATA  ( uart_prdata     ),
        .PREADY  ( uart_pready     ),
        .PSLVERR ( uart_pslverr    ),
        .INT     ( irq_sources[0]  ),
        .OUT1N   (                 ), // keep open
        .OUT2N   (                 ), // keep open
        .RTSN    (                 ), // no flow control
        .DTRN    (                 ), // no flow control
        .CTSN    ( 1'b0            ),
        .DSRN    ( 1'b0            ),
        .DCDN    ( 1'b0            ),
        .RIN     ( 1'b0            ),
        .SIN     ( rx_i            ),
        .SOUT    ( tx_o            )
    );

    // ---------------
    // Ethernet
    // ---------------
  //   xlnx_axi_ethernetlite i_xlnx_axi_ethernetlite (

  //   );

  // output   ip2intc_irpt;
  // input    s_axi_aclk;
  // input    s_axi_aresetn;
  // input [3:0]s_axi_awid;
  // input [12:0]s_axi_awaddr;
  // input [7:0]s_axi_awlen;
  // input [2:0]s_axi_awsize;
  // input [1:0]s_axi_awburst;
  // input [3:0]s_axi_awcache;
  // input s_axi_awvalid;
  // output s_axi_awready;
  // input [31:0]s_axi_wdata;
  // input [3:0]s_axi_wstrb;
  // input s_axi_wlast;
  // input s_axi_wvalid;
  // output s_axi_wready;
  // output [3:0]s_axi_bid;
  // output [1:0]s_axi_bresp;
  // output s_axi_bvalid;
  // input s_axi_bready;
  // input [3:0]s_axi_arid;
  // input [12:0]s_axi_araddr;
  // input [7:0]s_axi_arlen;
  // input [2:0]s_axi_arsize;
  // input [1:0]s_axi_arburst;
  // input [3:0]s_axi_arcache;
  // input s_axi_arvalid;
  // output s_axi_arready;
  // output [3:0]s_axi_rid;
  // output [31:0]s_axi_rdata;
  // output [1:0]s_axi_rresp;
  // output s_axi_rlast;
  // output s_axi_rvalid;
  // // input s_axi_rready;

  // input        phy_tx_clk   ( eth_txck   ),
  // input        phy_rx_clk   ( eth_rxck   ),
  // input        phy_crs      ( 1'b0       ),
  // input        phy_dv       ( eth_rxctl  ),
  // input [3:0]  phy_rx_data  ( eth_rxd    ),
  // input        phy_col      ( 1'b0       ),
  // input        phy_rx_er    ( 1'b0       ),
  // output       phy_rst_n    ( eth_rst_n  ),
  // output       phy_tx_en    ( eth_tx_en  ),
  // output [3:0] phy_tx_data  ( eth_txd    ),
  // input        phy_mdio_i   ( phy_mdio_i ),
  // output       phy_mdio_o   ( phy_mdio_o ),
  // output       phy_mdio_t   ( phy_mdio_t ),
  // output       phy_mdc      ( eth_mdc    )

  //   assign eth_mdio = phy_mdio_t ? phy_mdio_i : 1'bz;
  //   assign phy_mdio_i = phy_mdio_t ? 1'b0 : eth_mdio;

  //   // active low
  //   assign eth_int_b = 1'b1;
  //   // set floating - power management event
  //   assign eth_pme_b = 1'b1;

    // ---------------
    // SPI
    // ---------------
    logic [31:0] s_axi_spi_awaddr;
    logic [7:0]  s_axi_spi_awlen;
    logic [2:0]  s_axi_spi_awsize;
    logic [1:0]  s_axi_spi_awburst;
    logic [0:0]  s_axi_spi_awlock;
    logic [3:0]  s_axi_spi_awcache;
    logic [2:0]  s_axi_spi_awprot;
    logic [3:0]  s_axi_spi_awregion;
    logic [3:0]  s_axi_spi_awqos;
    logic        s_axi_spi_awvalid;
    logic        s_axi_spi_awready;
    logic [31:0] s_axi_spi_wdata;
    logic [3:0]  s_axi_spi_wstrb;
    logic        s_axi_spi_wlast;
    logic        s_axi_spi_wvalid;
    logic        s_axi_spi_wready;
    logic [1:0]  s_axi_spi_bresp;
    logic        s_axi_spi_bvalid;
    logic        s_axi_spi_bready;
    logic [31:0] s_axi_spi_araddr;
    logic [7:0]  s_axi_spi_arlen;
    logic [2:0]  s_axi_spi_arsize;
    logic [1:0]  s_axi_spi_arburst;
    logic [0:0]  s_axi_spi_arlock;
    logic [3:0]  s_axi_spi_arcache;
    logic [2:0]  s_axi_spi_arprot;
    logic [3:0]  s_axi_spi_arregion;
    logic [3:0]  s_axi_spi_arqos;
    logic        s_axi_spi_arvalid;
    logic        s_axi_spi_arready;
    logic [31:0] s_axi_spi_rdata;
    logic [1:0]  s_axi_spi_rresp;
    logic        s_axi_spi_rlast;
    logic        s_axi_spi_rvalid;
    logic        s_axi_spi_rready;

    if (InclSPI) begin : gen_spi
        axi_dwidth_converter_0 i_axi_dwidth_converter_spi (
            .s_axi_aclk     ( clk_i              ),
            .s_axi_aresetn  ( rst_ni             ),

            .s_axi_awid     ( spi.aw_id          ),
            .s_axi_awaddr   ( spi.aw_addr[31:0]  ),
            .s_axi_awlen    ( spi.aw_len         ),
            .s_axi_awsize   ( spi.aw_size        ),
            .s_axi_awburst  ( spi.aw_burst       ),
            .s_axi_awlock   ( spi.aw_lock        ),
            .s_axi_awcache  ( spi.aw_cache       ),
            .s_axi_awprot   ( spi.aw_prot        ),
            .s_axi_awregion ( spi.aw_region      ),
            .s_axi_awqos    ( spi.aw_qos         ),
            .s_axi_awvalid  ( spi.aw_valid       ),
            .s_axi_awready  ( spi.aw_ready       ),
            .s_axi_wdata    ( spi.w_data         ),
            .s_axi_wstrb    ( spi.w_strb         ),
            .s_axi_wlast    ( spi.w_last         ),
            .s_axi_wvalid   ( spi.w_valid        ),
            .s_axi_wready   ( spi.w_ready        ),
            .s_axi_bid      ( spi.b_id           ),
            .s_axi_bresp    ( spi.b_resp         ),
            .s_axi_bvalid   ( spi.b_valid        ),
            .s_axi_bready   ( spi.b_ready        ),
            .s_axi_arid     ( spi.ar_id          ),
            .s_axi_araddr   ( spi.ar_addr[31:0]  ),
            .s_axi_arlen    ( spi.ar_len         ),
            .s_axi_arsize   ( spi.ar_size        ),
            .s_axi_arburst  ( spi.ar_burst       ),
            .s_axi_arlock   ( spi.ar_lock        ),
            .s_axi_arcache  ( spi.ar_cache       ),
            .s_axi_arprot   ( spi.ar_prot        ),
            .s_axi_arregion ( spi.ar_region      ),
            .s_axi_arqos    ( spi.ar_qos         ),
            .s_axi_arvalid  ( spi.ar_valid       ),
            .s_axi_arready  ( spi.ar_ready       ),
            .s_axi_rid      ( spi.r_id           ),
            .s_axi_rdata    ( spi.r_data         ),
            .s_axi_rresp    ( spi.r_resp         ),
            .s_axi_rlast    ( spi.r_last         ),
            .s_axi_rvalid   ( spi.r_valid        ),
            .s_axi_rready   ( spi.r_ready        ),

            .m_axi_awaddr   ( s_axi_spi_awaddr   ),
            .m_axi_awlen    ( s_axi_spi_awlen    ),
            .m_axi_awsize   ( s_axi_spi_awsize   ),
            .m_axi_awburst  ( s_axi_spi_awburst  ),
            .m_axi_awlock   ( s_axi_spi_awlock   ),
            .m_axi_awcache  ( s_axi_spi_awcache  ),
            .m_axi_awprot   ( s_axi_spi_awprot   ),
            .m_axi_awregion ( s_axi_spi_awregion ),
            .m_axi_awqos    ( s_axi_spi_awqos    ),
            .m_axi_awvalid  ( s_axi_spi_awvalid  ),
            .m_axi_awready  ( s_axi_spi_awready  ),
            .m_axi_wdata    ( s_axi_spi_wdata    ),
            .m_axi_wstrb    ( s_axi_spi_wstrb    ),
            .m_axi_wlast    ( s_axi_spi_wlast    ),
            .m_axi_wvalid   ( s_axi_spi_wvalid   ),
            .m_axi_wready   ( s_axi_spi_wready   ),
            .m_axi_bresp    ( s_axi_spi_bresp    ),
            .m_axi_bvalid   ( s_axi_spi_bvalid   ),
            .m_axi_bready   ( s_axi_spi_bready   ),
            .m_axi_araddr   ( s_axi_spi_araddr   ),
            .m_axi_arlen    ( s_axi_spi_arlen    ),
            .m_axi_arsize   ( s_axi_spi_arsize   ),
            .m_axi_arburst  ( s_axi_spi_arburst  ),
            .m_axi_arlock   ( s_axi_spi_arlock   ),
            .m_axi_arcache  ( s_axi_spi_arcache  ),
            .m_axi_arprot   ( s_axi_spi_arprot   ),
            .m_axi_arregion ( s_axi_spi_arregion ),
            .m_axi_arqos    ( s_axi_spi_arqos    ),
            .m_axi_arvalid  ( s_axi_spi_arvalid  ),
            .m_axi_arready  ( s_axi_spi_arready  ),
            .m_axi_rdata    ( s_axi_spi_rdata    ),
            .m_axi_rresp    ( s_axi_spi_rresp    ),
            .m_axi_rlast    ( s_axi_spi_rlast    ),
            .m_axi_rvalid   ( s_axi_spi_rvalid   ),
            .m_axi_rready   ( s_axi_spi_rready   )
        );

        axi_quad_spi_0 i_axi_spi (
            .ext_spi_clk    ( clk_i                  ),
            .s_axi4_aclk    ( clk_i                  ),
            .s_axi4_aresetn ( rst_ni                 ),
            .s_axi4_awaddr  ( s_axi_spi_awaddr[23:0] ),
            .s_axi4_awlen   ( s_axi_spi_awlen        ),
            .s_axi4_awsize  ( s_axi_spi_awsize       ),
            .s_axi4_awburst ( s_axi_spi_awburst      ),
            .s_axi4_awlock  ( s_axi_spi_awlock       ),
            .s_axi4_awcache ( s_axi_spi_awcache      ),
            .s_axi4_awprot  ( s_axi_spi_awprot       ),
            .s_axi4_awvalid ( s_axi_spi_awvalid      ),
            .s_axi4_awready ( s_axi_spi_awready      ),
            .s_axi4_wdata   ( s_axi_spi_wdata        ),
            .s_axi4_wstrb   ( s_axi_spi_wstrb        ),
            .s_axi4_wlast   ( s_axi_spi_wlast        ),
            .s_axi4_wvalid  ( s_axi_spi_wvalid       ),
            .s_axi4_wready  ( s_axi_spi_wready       ),
            .s_axi4_bresp   ( s_axi_spi_bresp        ),
            .s_axi4_bvalid  ( s_axi_spi_bvalid       ),
            .s_axi4_bready  ( s_axi_spi_bready       ),
            .s_axi4_araddr  ( s_axi_spi_araddr[23:0] ),
            .s_axi4_arlen   ( s_axi_spi_arlen        ),
            .s_axi4_arsize  ( s_axi_spi_arsize       ),
            .s_axi4_arburst ( s_axi_spi_arburst      ),
            .s_axi4_arlock  ( s_axi_spi_arlock       ),
            .s_axi4_arcache ( s_axi_spi_arcache      ),
            .s_axi4_arprot  ( s_axi_spi_arprot       ),
            .s_axi4_arvalid ( s_axi_spi_arvalid      ),
            .s_axi4_arready ( s_axi_spi_arready      ),
            .s_axi4_rdata   ( s_axi_spi_rdata        ),
            .s_axi4_rresp   ( s_axi_spi_rresp        ),
            .s_axi4_rlast   ( s_axi_spi_rlast        ),
            .s_axi4_rvalid  ( s_axi_spi_rvalid       ),
            .s_axi4_rready  ( s_axi_spi_rready       ),

            .io0_i          ( '0                     ),
            .io0_o          ( spi_mosi               ),
            .io0_t          ( '0                     ),
            .io1_i          ( spi_miso               ),
            .io1_o          (                        ),
            .io1_t          ( '0                     ),
            .ss_i           ( '0                     ),
            .ss_o           ( spi_ss                 ),
            .ss_t           ( '0                     ),
            .ip2intc_irpt   ( irq_sources[1]         ),

            .cfgclk         ( spi_clk_o              ),
            .cfgmclk        (                        ),
            .eos            (                        ),
            .preq           (                        )
        );
    end else begin
        assign s_axi_spi_awready = 1'b1;
        assign s_axi_spi_wready = 1'b1;

        assign s_axi_spi_bresp = '0;
        assign s_axi_spi_bvalid = 1'b1;

        assign s_axi_spi_arready = 1'b1;
        assign s_axi_spi_rdata = '0;
        assign s_axi_spi_rresp = '0;
        assign s_axi_spi_rlast = 1'b1;
        assign s_axi_spi_rvalid = 1'b1;
    end
endmodule