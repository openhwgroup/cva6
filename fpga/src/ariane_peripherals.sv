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
    parameter AxiAddrWidth = -1,
    parameter AxiDataWidth = -1
)(
    input logic        clk_i,  // Clock
    input logic        rst_ni, // Asynchronous reset active low
    AXI_BUS.in         plic,
    AXI_BUS.in         uart,
    output logic [1:0] irq_o,
    // UART
    input  logic rx_i,
    output logic tx_o
);

    // ---------------
    // PLIC
    // ---------------
    logic [ariane_soc::NumTargets-1:0] irqs;
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
  // input s_axi_rready;

  // input        phy_tx_clk   ( eth_txck ),
  // input        phy_rx_clk   ( eth_rxck ),
  // input        phy_crs      ( ),
  // input        phy_dv       ( ),
  // input [3:0]  phy_rx_data  ( eth_rxd ),
  // input        phy_col      ( ),
  // input        phy_rx_er    ( ),
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

endmodule