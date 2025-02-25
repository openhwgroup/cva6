// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright 2024 PlanV Technology
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Intel Peripherals

`include "register_interface/assign.svh"
`include "register_interface/typedef.svh"

module cva6_peripherals #(
    parameter int AxiAddrWidth = -1,
    parameter int AxiDataWidth = -1,
    parameter int AxiIdWidth   = -1,
    parameter int AxiUserWidth = 1,
    parameter bit InclUART     = 1,
    parameter bit InclSPI      = 0,
    parameter bit InclEthernet = 0,
    parameter bit InclGPIO     = 0,
    parameter bit InclTimer    = 1
) (
    input  logic       clk_i           , // Clock
    input  logic       clk_200MHz_i    ,
    input  logic       rst_ni          , // Asynchronous reset active low
    AXI_BUS.Slave      plic            ,
    AXI_BUS.Slave      uart            ,
    AXI_BUS.Slave      spi             ,
    AXI_BUS.Slave      gpio            ,
    AXI_BUS.Slave      ethernet        ,
    AXI_BUS.Slave      timer           ,
    output logic [1:0] irq_o           ,
    // UART
    input  logic       rx_i            ,
    output logic       tx_o            ,
    // Ethernet
    input  logic       eth_clk_i       ,
    input  wire        eth_rxck        ,
    input  wire        eth_rxctl       ,
    input  wire [3:0]  eth_rxd         ,
    output wire        eth_txck        ,
    output wire        eth_txctl       ,
    output wire [3:0]  eth_txd         ,
    output wire        eth_rst_n       ,
    input  logic       phy_tx_clk_i    , // 125 MHz Clock
    // MDIO Interface
    inout  wire        eth_mdio        ,
    output logic       eth_mdc         ,
    // SPI
    output logic       spi_clk_o       ,
    output logic       spi_mosi        ,
    input  logic       spi_miso        ,
    output logic       spi_ss          ,
    // SD Card
    input  logic       sd_clk_i        ,
    output logic [7:0] leds_o          ,
    input  logic [7:0] dip_switches_i
);

    // ---------------
    // 1. PLIC
    // ---------------
    logic [ariane_soc::NumSources-1:0] irq_sources;

    // Unused interrupt sources
    assign irq_sources[ariane_soc::NumSources-1:7] = '0;

    REG_BUS #(
        .ADDR_WIDTH ( 32 ),
        .DATA_WIDTH ( 32 )
    ) reg_bus (clk_i);

    logic         plic_penable;
    logic         plic_pwrite;
    logic [31:0]  plic_paddr;
    logic         plic_psel;
    logic [31:0]  plic_pwdata;
    logic [31:0]  plic_prdata;
    logic         plic_pready;
    logic         plic_pslverr;

    axi2apb_64_32 #(
        .AXI4_ADDRESS_WIDTH ( AxiAddrWidth  ),
        .AXI4_RDATA_WIDTH   ( AxiDataWidth  ),
        .AXI4_WDATA_WIDTH   ( AxiDataWidth  ),
        .AXI4_ID_WIDTH      ( AxiIdWidth    ),
        .AXI4_USER_WIDTH    ( AxiUserWidth  ),
        .BUFF_DEPTH_SLAVE   ( 2             ),
        .APB_ADDR_WIDTH     ( 32            )
    ) i_axi2apb_64_32_plic (
        .ACLK      ( clk_i          ),
        .ARESETn   ( rst_ni         ),
        .test_en_i ( 1'b0           ),
        .AWID_i    ( plic.aw_id     ),
        .AWADDR_i  ( plic.aw_addr   ),
        .AWLEN_i   ( plic.aw_len    ),
        .AWSIZE_i  ( plic.aw_size   ),
        .AWBURST_i ( plic.aw_burst  ),
        .AWLOCK_i  ( plic.aw_lock   ),
        .AWCACHE_i ( plic.aw_cache  ),
        .AWPROT_i  ( plic.aw_prot   ),
        .AWREGION_i( plic.aw_region ),
        .AWUSER_i  ( plic.aw_user   ),
        .AWQOS_i   ( plic.aw_qos    ),
        .AWVALID_i ( plic.aw_valid  ),
        .AWREADY_o ( plic.aw_ready  ),
        .WDATA_i   ( plic.w_data    ),
        .WSTRB_i   ( plic.w_strb    ),
        .WLAST_i   ( plic.w_last    ),
        .WUSER_i   ( plic.w_user    ),
        .WVALID_i  ( plic.w_valid   ),
        .WREADY_o  ( plic.w_ready   ),
        .BID_o     ( plic.b_id      ),
        .BRESP_o   ( plic.b_resp    ),
        .BVALID_o  ( plic.b_valid   ),
        .BUSER_o   ( plic.b_user    ),
        .BREADY_i  ( plic.b_ready   ),
        .ARID_i    ( plic.ar_id     ),
        .ARADDR_i  ( plic.ar_addr   ),
        .ARLEN_i   ( plic.ar_len    ),
        .ARSIZE_i  ( plic.ar_size   ),
        .ARBURST_i ( plic.ar_burst  ),
        .ARLOCK_i  ( plic.ar_lock   ),
        .ARCACHE_i ( plic.ar_cache  ),
        .ARPROT_i  ( plic.ar_prot   ),
        .ARREGION_i( plic.ar_region ),
        .ARUSER_i  ( plic.ar_user   ),
        .ARQOS_i   ( plic.ar_qos    ),
        .ARVALID_i ( plic.ar_valid  ),
        .ARREADY_o ( plic.ar_ready  ),
        .RID_o     ( plic.r_id      ),
        .RDATA_o   ( plic.r_data    ),
        .RRESP_o   ( plic.r_resp    ),
        .RLAST_o   ( plic.r_last    ),
        .RUSER_o   ( plic.r_user    ),
        .RVALID_o  ( plic.r_valid   ),
        .RREADY_i  ( plic.r_ready   ),
        .PENABLE   ( plic_penable   ),
        .PWRITE    ( plic_pwrite    ),
        .PADDR     ( plic_paddr     ),
        .PSEL      ( plic_psel      ),
        .PWDATA    ( plic_pwdata    ),
        .PRDATA    ( plic_prdata    ),
        .PREADY    ( plic_pready    ),
        .PSLVERR   ( plic_pslverr   )
    );

    apb_to_reg i_apb_to_reg (
        .clk_i     ( clk_i        ),
        .rst_ni    ( rst_ni       ),
        .penable_i ( plic_penable ),
        .pwrite_i  ( plic_pwrite  ),
        .paddr_i   ( plic_paddr   ),
        .psel_i    ( plic_psel    ),
        .pwdata_i  ( plic_pwdata  ),
        .prdata_o  ( plic_prdata  ),
        .pready_o  ( plic_pready  ),
        .pslverr_o ( plic_pslverr ),
        .reg_o     ( reg_bus      )
    );

    // define reg type according to REG_BUS above
    `REG_BUS_TYPEDEF_ALL(plic, logic[31:0], logic[31:0], logic[3:0])
    plic_req_t plic_req;
    plic_rsp_t plic_rsp;

    // assign REG_BUS.out to (req_t, rsp_t) pair 
    `REG_BUS_ASSIGN_TO_REQ(plic_req, reg_bus)
    `REG_BUS_ASSIGN_FROM_RSP(reg_bus, plic_rsp)

    plic_top #(
      .N_SOURCE    ( ariane_soc::NumSources  ),
      .N_TARGET    ( ariane_soc::NumTargets  ),
      .MAX_PRIO    ( ariane_soc::MaxPriority ),
      .reg_req_t   ( plic_req_t              ),
      .reg_rsp_t   ( plic_rsp_t              )
    ) i_plic (
      .clk_i,
      .rst_ni,
      .req_i         ( plic_req    ),
      .resp_o        ( plic_rsp    ),
      .le_i          ( '0          ), // 0:level 1:edge
      .irq_sources_i ( irq_sources ),
      .eip_targets_o ( irq_o       )
    );

    // ---------------
    // 2. UART
    // ---------------

    // UART Through JTAG//

logic uart_amm_ready;
logic uart_amm_read;
logic uart_amm_write;
logic uart_amm_read_n;
logic uart_amm_write_n;
logic uart_amm_chipselect;
logic uart_amm_irq;
logic [0:0] uart_amm_address;
logic [31:0] uart_amm_rdata;
logic [31:0] uart_amm_wdata;


assign uart_amm_read_n = ~uart_amm_read;
assign uart_amm_write_n = ~uart_amm_write;

cva6_intel_jtag_uart_0 uart_i (
    .clk            (clk_i),            //   input,   width = 1,               clk.clk
    .rst_n          (rst_ni), 
    .av_chipselect  (uart_amm_chipselect),  //   input,   width = 1, avalon_jtag_slave.chipselect
    .av_address     (uart_amm_address),     //   input,   width = 1,                  .address
    .av_read_n      (uart_amm_read_n),      //   input,   width = 1,                  .read_n
    .av_readdata    (uart_amm_rdata),    //  output,  width = 32,                  .readdata
    .av_write_n     (uart_amm_write_n),     //   input,   width = 1,                  .write_n
    .av_writedata   (uart_amm_wdata),   //   input,  width = 32,                  .writedata
    .av_waitrequest (uart_amm_ready), //  output,   width = 1,                  .waitrequest
    .av_irq         (irq_sources[0])          //  output,   width = 1,               irq.irq
);

//axi4 to avalon converter
interconnect_altera_mm_interconnect_1920_v5r556a axi_to_avalon_uart (
		.axi_bridge_1_m0_awid                                             (uart.aw_id),                                        //   input,   width = 8,                                            axi_bridge_1_m0.awid
		.axi_bridge_1_m0_awaddr                                           (uart.aw_addr),                                      //   input,  width = 64,                                                           .awaddr
		.axi_bridge_1_m0_awlen                                            (uart.aw_len),                                       //   input,   width = 8,                                                           .awlen
		.axi_bridge_1_m0_awsize                                           (uart.aw_size),                                      //   input,   width = 3,                                                           .awsize
		.axi_bridge_1_m0_awburst                                          (uart.aw_burst),                                     //   input,   width = 2,                                                           .awburst
		.axi_bridge_1_m0_awlock                                           (uart.aw_lock),                                      //   input,   width = 1,                                                           .awlock
		.axi_bridge_1_m0_awcache                                          (uart.aw_cache),                                     //   input,   width = 4,                                                           .awcache
		.axi_bridge_1_m0_awprot                                           (uart.aw_prot),                                      //   input,   width = 3,                                                           .awprot
		.axi_bridge_1_m0_awvalid                                          (uart.aw_valid),                                     //   input,   width = 1,                                                           .awvalid
		.axi_bridge_1_m0_awready                                          (uart.aw_ready),                                     //  output,   width = 1,                                                           .awready
		.axi_bridge_1_m0_wdata                                            (uart.w_data),                                       //   input,  width = 64,                                                           .wdata
		.axi_bridge_1_m0_wstrb                                            (uart.w_strb),                                       //   input,   width = 8,                                                           .wstrb
		.axi_bridge_1_m0_wlast                                            (uart.w_last),                                       //   input,   width = 1,                                                           .wlast
		.axi_bridge_1_m0_wvalid                                           (uart.w_valid),                                      //   input,   width = 1,                                                           .wvalid
		.axi_bridge_1_m0_wready                                           (uart.w_ready),                                      //  output,   width = 1,                                                           .wready
		.axi_bridge_1_m0_bid                                              (uart.b_id),                                         //  output,   width = 8,                                                           .bid
		.axi_bridge_1_m0_bresp                                            (uart.b_resp),                                       //  output,   width = 2,                                                           .bresp
		.axi_bridge_1_m0_bvalid                                           (uart.b_valid),                                      //  output,   width = 1,                                                           .bvalid
		.axi_bridge_1_m0_bready                                           (uart.b_ready),                                      //   input,   width = 1,                                                           .bready
		.axi_bridge_1_m0_arid                                             (uart.ar_id),                                        //   input,   width = 8,                                                           .arid
		.axi_bridge_1_m0_araddr                                           (uart.ar_addr),                                      //   input,  width = 64,                                                           .araddr
		.axi_bridge_1_m0_arlen                                            (uart.ar_len),                                       //   input,   width = 8,                                                           .arlen
		.axi_bridge_1_m0_arsize                                           (uart.ar_size),                                      //   input,   width = 3,                                                           .arsize
		.axi_bridge_1_m0_arburst                                          (uart.ar_burst),                                     //   input,   width = 2,                                                           .arburst
		.axi_bridge_1_m0_arlock                                           (uart.ar_lock),                                      //   input,   width = 1,                                                           .arlock
		.axi_bridge_1_m0_arcache                                          (uart.ar_cache),                                     //   input,   width = 4,                                                           .arcache
		.axi_bridge_1_m0_arprot                                           (uart.ar_prot),                                      //   input,   width = 3,                                                           .arprot
		.axi_bridge_1_m0_arvalid                                          (uart.ar_valid),                                     //   input,   width = 1,                                                           .arvalid
		.axi_bridge_1_m0_arready                                          (uart.ar_ready),                                     //  output,   width = 1,                                                           .arready
		.axi_bridge_1_m0_rid                                              (uart.r_id),                                         //  output,   width = 8,                                                           .rid
		.axi_bridge_1_m0_rdata                                            (uart.r_data),                                       //  output,  width = 64,                                                           .rdata
		.axi_bridge_1_m0_rresp                                            (uart.r_resp),                                       //  output,   width = 2,                                                           .rresp
		.axi_bridge_1_m0_rlast                                            (uart.r_last),                                       //  output,   width = 1,                                                           .rlast
		.axi_bridge_1_m0_rvalid                                           (uart.r_valid),                                      //  output,   width = 1,                                                           .rvalid
		.axi_bridge_1_m0_rready                                           (uart.r_ready),                                      //   input,   width = 1,                                                           .rready
		.jtag_uart_0_avalon_jtag_slave_address                            (uart_amm_address),     //  output,   width = 1,                              jtag_uart_0_avalon_jtag_slave.address
		.jtag_uart_0_avalon_jtag_slave_write                              (uart_amm_write),       //  output,   width = 1,                                                           .write
		.jtag_uart_0_avalon_jtag_slave_read                               (uart_amm_read),        //  output,   width = 1,                                                           .read
		.jtag_uart_0_avalon_jtag_slave_readdata                           (uart_amm_rdata),    //   input,  width = 32,                                                           .readdata
		.jtag_uart_0_avalon_jtag_slave_writedata                          (uart_amm_wdata),   //  output,  width = 32,                                                           .writedata
		.jtag_uart_0_avalon_jtag_slave_waitrequest                        (uart_amm_ready), //   input,   width = 1,                                                           .waitrequest
		.jtag_uart_0_avalon_jtag_slave_chipselect                         (uart_amm_chipselect),  //  output,   width = 1,                                                           .chipselect
		.axi_bridge_1_clk_reset_reset_bridge_in_reset_reset               (~rst_ni),                              //   input,   width = 1,               axi_bridge_1_clk_reset_reset_bridge_in_reset.reset
		.axi_bridge_1_m0_translator_clk_reset_reset_bridge_in_reset_reset (~rst_ni),                              //   input,   width = 1, axi_bridge_1_m0_translator_clk_reset_reset_bridge_in_reset.reset
		.emif_fm_0_emif_usr_clk_clk                                       (clk_i)                                   //   input,   width = 1,                                     emif_fm_0_emif_usr_clk.clk
	);

    // ---------------
    // 3. SPI
    // ---------------
   assign spi.b_user = 1'b0;
   assign spi.r_user = 1'b0;

    if (InclSPI) begin : gen_spi
        logic         spi_penable;
        logic         spi_pwrite;
        logic [31:0]  spi_paddr;
        logic         spi_psel;
        logic [31:0]  spi_pwdata;
        logic [31:0]  spi_prdata;
        logic         spi_pready;
        logic         spi_pslverr;

        axi2apb_64_32 #(
            .AXI4_ADDRESS_WIDTH ( AxiAddrWidth ),
            .AXI4_RDATA_WIDTH   ( AxiDataWidth ),
            .AXI4_WDATA_WIDTH   ( AxiDataWidth ),
            .AXI4_ID_WIDTH      ( AxiIdWidth   ),
            .AXI4_USER_WIDTH    ( AxiUserWidth ),
            .BUFF_DEPTH_SLAVE   ( 2            ),
            .APB_ADDR_WIDTH     ( 32           )
        ) i_axi2apb_64_32_spi (
            .ACLK      ( clk_i          ),
            .ARESETn   ( rst_ni         ),
            .test_en_i ( 1'b0           ),
            .AWID_i    ( spi.aw_id     ),
            .AWADDR_i  ( spi.aw_addr   ),
            .AWLEN_i   ( spi.aw_len    ),
            .AWSIZE_i  ( spi.aw_size   ),
            .AWBURST_i ( spi.aw_burst  ),
            .AWLOCK_i  ( spi.aw_lock   ),
            .AWCACHE_i ( spi.aw_cache  ),
            .AWPROT_i  ( spi.aw_prot   ),
            .AWREGION_i( spi.aw_region ),
            .AWUSER_i  ( spi.aw_user   ),
            .AWQOS_i   ( spi.aw_qos    ),
            .AWVALID_i ( spi.aw_valid  ),
            .AWREADY_o ( spi.aw_ready  ),
            .WDATA_i   ( spi.w_data    ),
            .WSTRB_i   ( spi.w_strb    ),
            .WLAST_i   ( spi.w_last    ),
            .WUSER_i   ( spi.w_user    ),
            .WVALID_i  ( spi.w_valid   ),
            .WREADY_o  ( spi.w_ready   ),
            .BID_o     ( spi.b_id      ),
            .BRESP_o   ( spi.b_resp    ),
            .BVALID_o  ( spi.b_valid   ),
            // .BUSER_o   ( spi.b_user    ),
            .BREADY_i  ( spi.b_ready   ),
            .ARID_i    ( spi.ar_id     ),
            .ARADDR_i  ( spi.ar_addr   ),
            .ARLEN_i   ( spi.ar_len    ),
            .ARSIZE_i  ( spi.ar_size   ),
            .ARBURST_i ( spi.ar_burst  ),
            .ARLOCK_i  ( spi.ar_lock   ),
            .ARCACHE_i ( spi.ar_cache  ),
            .ARPROT_i  ( spi.ar_prot   ),
            .ARREGION_i( spi.ar_region ),
            .ARUSER_i  ( spi.ar_user   ),
            .ARQOS_i   ( spi.ar_qos    ),
            .ARVALID_i ( spi.ar_valid  ),
            .ARREADY_o ( spi.ar_ready  ),
            .RID_o     ( spi.r_id      ),
            .RDATA_o   ( spi.r_data    ),
            .RRESP_o   ( spi.r_resp    ),
            .RLAST_o   ( spi.r_last    ),
            // .RUSER_o   ( spi.r_user    ),
            .RVALID_o  ( spi.r_valid   ),
            .RREADY_i  ( spi.r_ready   ),
            .PENABLE   ( spi_penable   ),
            .PWRITE    ( spi_pwrite    ),
            .PADDR     ( spi_paddr     ),
            .PSEL      ( spi_psel      ),
            .PWDATA    ( spi_pwdata    ),
            .PRDATA    ( spi_prdata    ),
            .PREADY    ( spi_pready    ),
            .PSLVERR   ( spi_pslverr   )
        );

        apb_spi_master #(
            .BUFFER_DEPTH  (10),
            .APB_ADDR_WIDTH(32)  //APB slaves are 4KB by default
        ) SPI0(
            .HCLK(clk_i),
            .HRESETn(rst_ni),
            .PADDR(spi_paddr),
            .PWDATA(spi_pwdata),
            .PWRITE(spi_pwrite),
            .PSEL(spi_psel),
            .PENABLE(spi_penable),
            .PRDATA(spi_prdata),
            .PREADY(spi_pready),
            .PSLVERR(spi_pslverr),
            .events_o(irq_sources[1]),
            .spi_mode(  ),
            .spi_clk(spi_clk_o),
            .spi_csn0(spi_ss),
            .spi_sdo0(spi_mosi),
            .spi_sdi0(  ),
            .spi_csn1(  ),
            .spi_sdo1(  ),
            .spi_sdi1(spi_miso),
            .spi_csn2(  ),
            .spi_sdo2(  ),
            .spi_sdi2(  ),
            .spi_csn3(  ),
            .spi_sdo3(  ),
            .spi_sdi3(  )
        );

    end else begin
        assign spi_clk_o = 1'b0;
        assign spi_mosi = 1'b0;
        assign spi_ss = 1'b0;

        // assign irq_sources [1] = 1'b0;
        assign spi.aw_ready = 1'b1;
        assign spi.ar_ready = 1'b1;
        assign spi.w_ready = 1'b1;

        assign spi.b_valid = spi.aw_valid;
        assign spi.b_id = spi.aw_id;
        assign spi.b_resp = axi_pkg::RESP_SLVERR;
        assign spi.b_user = '0;

        assign spi.r_valid = spi.ar_valid;
        assign spi.r_resp = axi_pkg::RESP_SLVERR;
        assign spi.r_data = 'hdeadbeef;
        assign spi.r_last = 1'b1;
    end


    // ---------------
    // 4. Ethernet
    // ---------------

    if (InclEthernet) begin : gen_ethernet

    logic                    clk_200_int, clk_rgmii, clk_rgmii_quad;
    logic                    eth_en, eth_we, eth_int_n, eth_pme_n, eth_mdio_i, eth_mdio_o, eth_mdio_oe;
    logic [AxiAddrWidth-1:0] eth_addr;
    logic [AxiDataWidth-1:0] eth_wrdata, eth_rdata;
    logic [AxiDataWidth/8-1:0] eth_be;

    axi2mem #(
        .AXI_ID_WIDTH   ( AxiIdWidth       ),
        .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
        .AXI_DATA_WIDTH ( AxiDataWidth     ),
        .AXI_USER_WIDTH ( AxiUserWidth     )
    ) i_axi2rom (
        .clk_i  ( clk_i                   ),
        .rst_ni ( rst_ni                  ),
        .slave  ( ethernet                ),
        .req_o  ( eth_en                  ),
        .we_o   ( eth_we                  ),
        .addr_o ( eth_addr                ),
        .be_o   ( eth_be                  ),
        .data_o ( eth_wrdata              ),
        .data_i ( eth_rdata               )
    );

    framing_top  #(
        .TARGET("ALTERA")
    ) eth_rgmii (
       .msoc_clk(clk_i),
       .core_lsu_addr(eth_addr[14:0]),
       .core_lsu_wdata(eth_wrdata),
       .core_lsu_be(eth_be),
       .ce_d(eth_en),
       .we_d(eth_en & eth_we),
       .framing_sel(eth_en),
       .framing_rdata(eth_rdata),
       .rst_int(!rst_ni),
       .clk_int(phy_tx_clk_i), // 125 MHz in-phase
       .clk90_int(eth_clk_i),    // 125 MHz quadrature
       .clk_200_int(clk_200MHz_i),
       /*
        * Ethernet: 1000BASE-T RGMII
        */
       .phy_rx_clk(eth_rxck),
       .phy_rxd(eth_rxd),
       .phy_rx_ctl(eth_rxctl),
       .phy_tx_clk(eth_txck),
       .phy_txd(eth_txd),
       .phy_tx_ctl(eth_txctl),
       .phy_reset_n(eth_rst_n),
       .phy_int_n(eth_int_n),
       .phy_pme_n(eth_pme_n),
       .phy_mdc(eth_mdc),
       .phy_mdio_i(eth_mdio_i),
       .phy_mdio_o(eth_mdio_o),
       .phy_mdio_oe(eth_mdio_oe),
       .eth_irq(irq_sources[2])
    );

    iobuf iobuf_inst (
		.dout   (eth_mdio_i),   //  output,  width = 1,   dout.export
		.din    (eth_mdio_o),    //   input,  width = 1,    din.export
		.oe     (~eth_mdio_oe),     //   input,  width = 1,     oe.export
		.pad_io (eth_mdio)  //   inout,  width = 1, pad_io.export
	);

    end else begin
        assign irq_sources [2] = 1'b0;
        assign ethernet.aw_ready = 1'b1;
        assign ethernet.ar_ready = 1'b1;
        assign ethernet.w_ready = 1'b1;

        assign ethernet.b_valid = ethernet.aw_valid;
        assign ethernet.b_id = ethernet.aw_id;
        assign ethernet.b_resp = axi_pkg::RESP_SLVERR;
        assign ethernet.b_user = '0;

        assign ethernet.r_valid = ethernet.ar_valid;
        assign ethernet.r_resp = axi_pkg::RESP_SLVERR;
        assign ethernet.r_data = 'hdeadbeef;
        assign ethernet.r_last = 1'b1;
    end

    // 5. GPIO
    assign gpio.b_user = 1'b0;
    assign gpio.r_user = 1'b0;

    if (InclGPIO) begin : gen_gpio

        logic         gpio_penable;
        logic         gpio_pwrite;
        logic [31:0]  gpio_paddr;
        logic         gpio_psel;
        logic [31:0]  gpio_pwdata;
        logic [31:0]  gpio_prdata;
        logic         gpio_pready;
        logic         gpio_pslverr;

        axi2apb_64_32 #(
            .AXI4_ADDRESS_WIDTH ( AxiAddrWidth ),
            .AXI4_RDATA_WIDTH   ( AxiDataWidth ),
            .AXI4_WDATA_WIDTH   ( AxiDataWidth ),
            .AXI4_ID_WIDTH      ( AxiIdWidth   ),
            .AXI4_USER_WIDTH    ( AxiUserWidth ),
            .BUFF_DEPTH_SLAVE   ( 2            ),
            .APB_ADDR_WIDTH     ( 32           )
        ) i_axi2apb_64_32_gpio (
            .ACLK      ( clk_i          ),
            .ARESETn   ( rst_ni         ),
            .test_en_i ( 1'b0           ),
            .AWID_i    ( gpio.aw_id     ),
            .AWADDR_i  ( gpio.aw_addr   ),
            .AWLEN_i   ( gpio.aw_len    ),
            .AWSIZE_i  ( gpio.aw_size   ),
            .AWBURST_i ( gpio.aw_burst  ),
            .AWLOCK_i  ( gpio.aw_lock   ),
            .AWCACHE_i ( gpio.aw_cache  ),
            .AWPROT_i  ( gpio.aw_prot   ),
            .AWREGION_i( gpio.aw_region ),
            .AWUSER_i  ( gpio.aw_user   ),
            .AWQOS_i   ( gpio.aw_qos    ),
            .AWVALID_i ( gpio.aw_valid  ),
            .AWREADY_o ( gpio.aw_ready  ),
            .WDATA_i   ( gpio.w_data    ),
            .WSTRB_i   ( gpio.w_strb    ),
            .WLAST_i   ( gpio.w_last    ),
            .WUSER_i   ( gpio.w_user    ),
            .WVALID_i  ( gpio.w_valid   ),
            .WREADY_o  ( gpio.w_ready   ),
            .BID_o     ( gpio.b_id      ),
            .BRESP_o   ( gpio.b_resp    ),
            .BVALID_o  ( gpio.b_valid   ),
            // .BUSER_o   ( gpio.b_user    ),
            .BREADY_i  ( gpio.b_ready   ),
            .ARID_i    ( gpio.ar_id     ),
            .ARADDR_i  ( gpio.ar_addr   ),
            .ARLEN_i   ( gpio.ar_len    ),
            .ARSIZE_i  ( gpio.ar_size   ),
            .ARBURST_i ( gpio.ar_burst  ),
            .ARLOCK_i  ( gpio.ar_lock   ),
            .ARCACHE_i ( gpio.ar_cache  ),
            .ARPROT_i  ( gpio.ar_prot   ),
            .ARREGION_i( gpio.ar_region ),
            .ARUSER_i  ( gpio.ar_user   ),
            .ARQOS_i   ( gpio.ar_qos    ),
            .ARVALID_i ( gpio.ar_valid  ),
            .ARREADY_o ( gpio.ar_ready  ),
            .RID_o     ( gpio.r_id      ),
            .RDATA_o   ( gpio.r_data    ),
            .RRESP_o   ( gpio.r_resp    ),
            .RLAST_o   ( gpio.r_last    ),
            // .RUSER_o   ( gpio.r_user    ),
            .RVALID_o  ( gpio.r_valid   ),
            .RREADY_i  ( gpio.r_ready   ),
            .PENABLE   ( gpio_penable   ),
            .PWRITE    ( gpio_pwrite    ),
            .PADDR     ( gpio_paddr     ),
            .PSEL      ( gpio_psel      ),
            .PWDATA    ( gpio_pwdata    ),
            .PRDATA    ( gpio_prdata    ),
            .PREADY    ( gpio_pready    ),
            .PSLVERR   ( gpio_pslverr   )
        );

        APB #(.ADDR_WIDTH ( 32 ),
            .DATA_WIDTH ( 32 )
        ) apb_gpio();
        assign apb_gpio.paddr   = gpio_paddr;
        assign apb_gpio.pprot   = 3'b0;
        assign apb_gpio.psel    = gpio_psel;
        assign apb_gpio.penable = gpio_penable;
        assign apb_gpio.pwrite  = gpio_pwrite;
        assign apb_gpio.pwdata  = gpio_pwdata;
        assign apb_gpio.pstrb   = {4{gpio_pwrite}};
        assign gpio_prdata      = apb_gpio.prdata;
        assign gpio_pready      = apb_gpio.pready;
        assign gpio_pslverr     = apb_gpio.pslverr;

        gpio_apb_wrap_intf # (
            .ADDR_WIDTH(32),
            // DATA_WIDTH of the APB interface
            .DATA_WIDTH(32)
        ) i_gpio(
            .clk_i(clk_i),
            .rst_ni(rst_ni),
            .gpio_in('0),
            .gpio_out(leds_o),
            .gpio_tx_en_o(), // 0 -> input, 1 -> output
            .gpio_in_sync_o(), // sampled and synchronized GPIO
            // input.
            .global_interrupt_o(),
            .pin_level_interrupts_o(),
            .apb_slave (apb_gpio)
        );
        
    end

    // 6. Timer
    if (InclTimer) begin : gen_timer
        logic         timer_penable;
        logic         timer_pwrite;
        logic [31:0]  timer_paddr;
        logic         timer_psel;
        logic [31:0]  timer_pwdata;
        logic [31:0]  timer_prdata;
        logic         timer_pready;
        logic         timer_pslverr;

        axi2apb_64_32 #(
            .AXI4_ADDRESS_WIDTH ( AxiAddrWidth ),
            .AXI4_RDATA_WIDTH   ( AxiDataWidth ),
            .AXI4_WDATA_WIDTH   ( AxiDataWidth ),
            .AXI4_ID_WIDTH      ( AxiIdWidth   ),
            .AXI4_USER_WIDTH    ( AxiUserWidth ),
            .BUFF_DEPTH_SLAVE   ( 2            ),
            .APB_ADDR_WIDTH     ( 32           )
        ) i_axi2apb_64_32_timer (
            .ACLK      ( clk_i           ),
            .ARESETn   ( rst_ni          ),
            .test_en_i ( 1'b0            ),
            .AWID_i    ( timer.aw_id     ),
            .AWADDR_i  ( timer.aw_addr   ),
            .AWLEN_i   ( timer.aw_len    ),
            .AWSIZE_i  ( timer.aw_size   ),
            .AWBURST_i ( timer.aw_burst  ),
            .AWLOCK_i  ( timer.aw_lock   ),
            .AWCACHE_i ( timer.aw_cache  ),
            .AWPROT_i  ( timer.aw_prot   ),
            .AWREGION_i( timer.aw_region ),
            .AWUSER_i  ( timer.aw_user   ),
            .AWQOS_i   ( timer.aw_qos    ),
            .AWVALID_i ( timer.aw_valid  ),
            .AWREADY_o ( timer.aw_ready  ),
            .WDATA_i   ( timer.w_data    ),
            .WSTRB_i   ( timer.w_strb    ),
            .WLAST_i   ( timer.w_last    ),
            .WUSER_i   ( timer.w_user    ),
            .WVALID_i  ( timer.w_valid   ),
            .WREADY_o  ( timer.w_ready   ),
            .BID_o     ( timer.b_id      ),
            .BRESP_o   ( timer.b_resp    ),
            .BVALID_o  ( timer.b_valid   ),
            .BUSER_o   ( timer.b_user    ),
            .BREADY_i  ( timer.b_ready   ),
            .ARID_i    ( timer.ar_id     ),
            .ARADDR_i  ( timer.ar_addr   ),
            .ARLEN_i   ( timer.ar_len    ),
            .ARSIZE_i  ( timer.ar_size   ),
            .ARBURST_i ( timer.ar_burst  ),
            .ARLOCK_i  ( timer.ar_lock   ),
            .ARCACHE_i ( timer.ar_cache  ),
            .ARPROT_i  ( timer.ar_prot   ),
            .ARREGION_i( timer.ar_region ),
            .ARUSER_i  ( timer.ar_user   ),
            .ARQOS_i   ( timer.ar_qos    ),
            .ARVALID_i ( timer.ar_valid  ),
            .ARREADY_o ( timer.ar_ready  ),
            .RID_o     ( timer.r_id      ),
            .RDATA_o   ( timer.r_data    ),
            .RRESP_o   ( timer.r_resp    ),
            .RLAST_o   ( timer.r_last    ),
            .RUSER_o   ( timer.r_user    ),
            .RVALID_o  ( timer.r_valid   ),
            .RREADY_i  ( timer.r_ready   ),
            .PENABLE   ( timer_penable   ),
            .PWRITE    ( timer_pwrite    ),
            .PADDR     ( timer_paddr     ),
            .PSEL      ( timer_psel      ),
            .PWDATA    ( timer_pwdata    ),
            .PRDATA    ( timer_prdata    ),
            .PREADY    ( timer_pready    ),
            .PSLVERR   ( timer_pslverr   )
        );

        apb_timer #(
                .APB_ADDR_WIDTH ( 32 ),
                .TIMER_CNT      ( 2  )
        ) i_timer (
            .HCLK    ( clk_i            ),
            .HRESETn ( rst_ni           ),
            .PSEL    ( timer_psel       ),
            .PENABLE ( timer_penable    ),
            .PWRITE  ( timer_pwrite     ),
            .PADDR   ( timer_paddr      ),
            .PWDATA  ( timer_pwdata     ),
            .PRDATA  ( timer_prdata     ),
            .PREADY  ( timer_pready     ),
            .PSLVERR ( timer_pslverr    ),
            .irq_o   ( irq_sources[6:3] )
        );
    end
endmodule
