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
    parameter int AxiIdWidth   = -1,
    parameter int AxiUserWidth = 1,
    parameter bit InclUART     = 1,
    parameter bit InclSPI      = 0,
    parameter bit InclEthernet = 0,
    parameter bit InclGPIO     = 0
) (
    input  logic       clk_i           , // Clock
    input  logic       clk_200MHz_i    ,
    input  logic       rst_ni          , // Asynchronous reset active low
    AXI_BUS.in         plic            ,
    AXI_BUS.in         uart            ,
    AXI_BUS.in         spi             ,
    AXI_BUS.in         gpio            ,
    input  logic       eth_clk_i       ,
    AXI_BUS.in         ethernet        ,
    output logic [1:0] irq_o           ,
    // UART
    input  logic       rx_i            ,
    output logic       tx_o            ,
    // Ethernet
    input  wire        eth_rxck        ,
    input  wire        eth_rxctl       ,
    input  wire [3:0]  eth_rxd         ,
    output wire        eth_txck        ,
    output wire        eth_txctl       ,
    output wire [3:0]  eth_txd         ,
    output wire        eth_rst_n       ,
    input  logic       phy_tx_clk_i    , // 25 MHz Clock
    // MDIO Interface
    inout  wire        eth_mdio        ,
    output logic       eth_mdc         ,
    // SPI
    output logic       spi_clk_o       ,
    output logic       spi_mosi        ,
    input  logic       spi_miso        ,
    output logic       spi_ss          ,
    output logic [7:0] leds_o          ,
    input  logic [7:0] dip_switches_i
);

    // ---------------
    // 1. PLIC
    // ---------------
    logic [ariane_soc::NumSources-1:0] irq_sources;

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

    plic #(
        .ID_BITWIDTH        ( ariane_soc::PLICIdWidth       ),
        .PARAMETER_BITWIDTH ( ariane_soc::ParameterBitwidth ),
        .NUM_TARGETS        ( ariane_soc::NumTargets        ),
        .NUM_SOURCES        ( ariane_soc::NumSources        )
    ) i_plic (
        .clk_i              ( clk_i                  ),
        .rst_ni             ( rst_ni                 ),
        .irq_sources_i      ( irq_sources            ),
        .eip_targets_o      ( irq_o                  ),
        .external_bus_io    ( reg_bus                )
    );

    // ---------------
    // 2. UART
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
        .AXI4_ADDRESS_WIDTH ( AxiAddrWidth ),
        .AXI4_RDATA_WIDTH   ( AxiDataWidth ),
        .AXI4_WDATA_WIDTH   ( AxiDataWidth ),
        .AXI4_ID_WIDTH      ( AxiIdWidth   ),
        .AXI4_USER_WIDTH    ( AxiUserWidth ),
        .BUFF_DEPTH_SLAVE   ( 2            ),
        .APB_ADDR_WIDTH     ( 32           )
    ) i_axi2apb_64_32_uart (
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

    if (InclUART) begin : gen_uart
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
    end else begin
        /* pragma translate_off */
        `ifndef VERILATOR
        mock_uart i_mock_uart (
            .clk_i     ( clk_i        ),
            .rst_ni    ( rst_ni       ),
            .penable_i ( uart_penable ),
            .pwrite_i  ( uart_pwrite  ),
            .paddr_i   ( uart_paddr   ),
            .psel_i    ( uart_psel    ),
            .pwdata_i  ( uart_pwdata  ),
            .prdata_o  ( uart_prdata  ),
            .pready_o  ( uart_pready  ),
            .pslverr_o ( uart_pslverr )
        );
        `endif
        /* pragma translate_on */
    end

    // ---------------
    // 3. SPI
    // ---------------
    assign spi.b_user = 1'b0;
    assign spi.r_user = 1'b0;

    if (InclSPI) begin : gen_spi
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

        xlnx_axi_dwidth_converter i_xlnx_axi_dwidth_converter_spi (
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

        xlnx_axi_quad_spi i_xlnx_axi_quad_spi (
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
            .io0_t          (                        ),
            .io1_i          ( spi_miso               ),
            .io1_o          (                        ),
            .io1_t          (                        ),
            .ss_i           ( '0                     ),
            .ss_o           ( spi_ss                 ),
            .ss_t           (                        ),
            .sck_o          ( spi_clk_o              ),
            .sck_i          ( '0                     ),
            .sck_t          (                        ),
            .ip2intc_irpt   ( irq_sources[1]         )
        );
    end else begin
        assign spi_clk_o = 1'b0;
        assign spi_mosi = 1'b0;
        assign spi_ss = 1'b0;

        assign irq_sources [1] = 1'b0;
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
    assign ethernet.b_user = 1'b0;
    assign ethernet.r_user = 1'b0;

    if (InclEthernet) begin : gen_ethernet

        AXI_BUS #(
            .AXI_ADDR_WIDTH ( AxiAddrWidth ),
            .AXI_DATA_WIDTH ( AxiDataWidth ),
            .AXI_ID_WIDTH   ( AxiIdWidth   ),
            .AXI_USER_WIDTH ( AxiUserWidth )
        ) axi_ethernet_cdc();

        logic s_eth_rst_n;

        logic [31:0] s_axi_eth_awaddr;
        logic [7:0]  s_axi_eth_awlen;
        logic [2:0]  s_axi_eth_awsize;
        logic [1:0]  s_axi_eth_awburst;
        logic [3:0]  s_axi_eth_awcache;
        logic        s_axi_eth_awvalid;
        logic        s_axi_eth_awready;
        logic [31:0] s_axi_eth_wdata;
        logic [3:0]  s_axi_eth_wstrb;
        logic        s_axi_eth_wlast;
        logic        s_axi_eth_wvalid;
        logic        s_axi_eth_wready;
        logic [1:0]  s_axi_eth_bresp;
        logic        s_axi_eth_bvalid;
        logic        s_axi_eth_bready;
        logic [31:0] s_axi_eth_araddr;
        logic [7:0]  s_axi_eth_arlen;
        logic [2:0]  s_axi_eth_arsize;
        logic [1:0]  s_axi_eth_arburst;
        logic [3:0]  s_axi_eth_arcache;
        logic        s_axi_eth_arvalid;
        logic        s_axi_eth_arready;
        logic [31:0] s_axi_eth_rdata;
        logic [1:0]  s_axi_eth_rresp;
        logic        s_axi_eth_rlast;
        logic        s_axi_eth_rvalid;

        rstgen i_rstgen (
            .clk_i        ( eth_clk_i   ),
            .rst_ni       ( rst_ni      ),
            .test_mode_i  ( test_en     ),
            .rst_no       ( s_eth_rst_n ),
            .init_no      (             ) // keep open
        );

        xlnx_axi_clock_converter i_xlnx_axi_clock_converter_ethernet (
          .s_axi_aclk     ( clk_i              ),
          .s_axi_aresetn  ( rst_ni             ),
          .s_axi_awid     ( ethernet.aw_id     ),
          .s_axi_awaddr   ( ethernet.aw_addr   ),
          .s_axi_awlen    ( ethernet.aw_len    ),
          .s_axi_awsize   ( ethernet.aw_size   ),
          .s_axi_awburst  ( ethernet.aw_burst  ),
          .s_axi_awlock   ( ethernet.aw_lock   ),
          .s_axi_awcache  ( ethernet.aw_cache  ),
          .s_axi_awprot   ( ethernet.aw_prot   ),
          .s_axi_awregion ( ethernet.aw_region ),
          .s_axi_awqos    ( ethernet.aw_qos    ),
          .s_axi_awvalid  ( ethernet.aw_valid  ),
          .s_axi_awready  ( ethernet.aw_ready  ),
          .s_axi_wdata    ( ethernet.w_data    ),
          .s_axi_wstrb    ( ethernet.w_strb    ),
          .s_axi_wlast    ( ethernet.w_last    ),
          .s_axi_wvalid   ( ethernet.w_valid   ),
          .s_axi_wready   ( ethernet.w_ready   ),
          .s_axi_bid      ( ethernet.b_id      ),
          .s_axi_bresp    ( ethernet.b_resp    ),
          .s_axi_bvalid   ( ethernet.b_valid   ),
          .s_axi_bready   ( ethernet.b_ready   ),
          .s_axi_arid     ( ethernet.ar_id     ),
          .s_axi_araddr   ( ethernet.ar_addr   ),
          .s_axi_arlen    ( ethernet.ar_len    ),
          .s_axi_arsize   ( ethernet.ar_size   ),
          .s_axi_arburst  ( ethernet.ar_burst  ),
          .s_axi_arlock   ( ethernet.ar_lock   ),
          .s_axi_arcache  ( ethernet.ar_cache  ),
          .s_axi_arprot   ( ethernet.ar_prot   ),
          .s_axi_arregion ( ethernet.ar_region ),
          .s_axi_arqos    ( ethernet.ar_qos    ),
          .s_axi_arvalid  ( ethernet.ar_valid  ),
          .s_axi_arready  ( ethernet.ar_ready  ),
          .s_axi_rid      ( ethernet.r_id      ),
          .s_axi_rdata    ( ethernet.r_data    ),
          .s_axi_rresp    ( ethernet.r_resp    ),
          .s_axi_rlast    ( ethernet.r_last    ),
          .s_axi_rvalid   ( ethernet.r_valid   ),
          .s_axi_rready   ( ethernet.r_ready   ),
          // to size converter
          .m_axi_aclk     ( eth_clk_i                  ),
          .m_axi_aresetn  ( s_eth_rst_n                ),
          .m_axi_awid     ( axi_ethernet_cdc.aw_id     ),
          .m_axi_awaddr   ( axi_ethernet_cdc.aw_addr   ),
          .m_axi_awlen    ( axi_ethernet_cdc.aw_len    ),
          .m_axi_awsize   ( axi_ethernet_cdc.aw_size   ),
          .m_axi_awburst  ( axi_ethernet_cdc.aw_burst  ),
          .m_axi_awlock   ( axi_ethernet_cdc.aw_lock   ),
          .m_axi_awcache  ( axi_ethernet_cdc.aw_cache  ),
          .m_axi_awprot   ( axi_ethernet_cdc.aw_prot   ),
          .m_axi_awregion ( axi_ethernet_cdc.aw_region ),
          .m_axi_awqos    ( axi_ethernet_cdc.aw_qos    ),
          .m_axi_awvalid  ( axi_ethernet_cdc.aw_valid  ),
          .m_axi_awready  ( axi_ethernet_cdc.aw_ready  ),
          .m_axi_wdata    ( axi_ethernet_cdc.w_data    ),
          .m_axi_wstrb    ( axi_ethernet_cdc.w_strb    ),
          .m_axi_wlast    ( axi_ethernet_cdc.w_last    ),
          .m_axi_wvalid   ( axi_ethernet_cdc.w_valid   ),
          .m_axi_wready   ( axi_ethernet_cdc.w_ready   ),
          .m_axi_bid      ( axi_ethernet_cdc.b_id      ),
          .m_axi_bresp    ( axi_ethernet_cdc.b_resp    ),
          .m_axi_bvalid   ( axi_ethernet_cdc.b_valid   ),
          .m_axi_bready   ( axi_ethernet_cdc.b_ready   ),
          .m_axi_arid     ( axi_ethernet_cdc.ar_id     ),
          .m_axi_araddr   ( axi_ethernet_cdc.ar_addr   ),
          .m_axi_arlen    ( axi_ethernet_cdc.ar_len    ),
          .m_axi_arsize   ( axi_ethernet_cdc.ar_size   ),
          .m_axi_arburst  ( axi_ethernet_cdc.ar_burst  ),
          .m_axi_arlock   ( axi_ethernet_cdc.ar_lock   ),
          .m_axi_arcache  ( axi_ethernet_cdc.ar_cache  ),
          .m_axi_arprot   ( axi_ethernet_cdc.ar_prot   ),
          .m_axi_arregion ( axi_ethernet_cdc.ar_region ),
          .m_axi_arqos    ( axi_ethernet_cdc.ar_qos    ),
          .m_axi_arvalid  ( axi_ethernet_cdc.ar_valid  ),
          .m_axi_arready  ( axi_ethernet_cdc.ar_ready  ),
          .m_axi_rid      ( axi_ethernet_cdc.r_id      ),
          .m_axi_rdata    ( axi_ethernet_cdc.r_data    ),
          .m_axi_rresp    ( axi_ethernet_cdc.r_resp    ),
          .m_axi_rlast    ( axi_ethernet_cdc.r_last    ),
          .m_axi_rvalid   ( axi_ethernet_cdc.r_valid   ),
          .m_axi_rready   ( axi_ethernet_cdc.r_ready   )
        );

        // system-bus is 64-bit, convert down to 32 bit
        xlnx_axi_dwidth_converter i_xlnx_axi_dwidth_converter_ethernet (
            .s_axi_aclk     ( eth_clk_i                      ),
            .s_axi_aresetn  ( s_eth_rst_n                    ),
            .s_axi_awid     ( axi_ethernet_cdc.aw_id         ),
            .s_axi_awaddr   ( axi_ethernet_cdc.aw_addr[31:0] ),
            .s_axi_awlen    ( axi_ethernet_cdc.aw_len        ),
            .s_axi_awsize   ( axi_ethernet_cdc.aw_size       ),
            .s_axi_awburst  ( axi_ethernet_cdc.aw_burst      ),
            .s_axi_awlock   ( axi_ethernet_cdc.aw_lock       ),
            .s_axi_awcache  ( axi_ethernet_cdc.aw_cache      ),
            .s_axi_awprot   ( axi_ethernet_cdc.aw_prot       ),
            .s_axi_awregion ( axi_ethernet_cdc.aw_region     ),
            .s_axi_awqos    ( axi_ethernet_cdc.aw_qos        ),
            .s_axi_awvalid  ( axi_ethernet_cdc.aw_valid      ),
            .s_axi_awready  ( axi_ethernet_cdc.aw_ready      ),
            .s_axi_wdata    ( axi_ethernet_cdc.w_data        ),
            .s_axi_wstrb    ( axi_ethernet_cdc.w_strb        ),
            .s_axi_wlast    ( axi_ethernet_cdc.w_last        ),
            .s_axi_wvalid   ( axi_ethernet_cdc.w_valid       ),
            .s_axi_wready   ( axi_ethernet_cdc.w_ready       ),
            .s_axi_bid      ( axi_ethernet_cdc.b_id          ),
            .s_axi_bresp    ( axi_ethernet_cdc.b_resp        ),
            .s_axi_bvalid   ( axi_ethernet_cdc.b_valid       ),
            .s_axi_bready   ( axi_ethernet_cdc.b_ready       ),
            .s_axi_arid     ( axi_ethernet_cdc.ar_id         ),
            .s_axi_araddr   ( axi_ethernet_cdc.ar_addr[31:0] ),
            .s_axi_arlen    ( axi_ethernet_cdc.ar_len        ),
            .s_axi_arsize   ( axi_ethernet_cdc.ar_size       ),
            .s_axi_arburst  ( axi_ethernet_cdc.ar_burst      ),
            .s_axi_arlock   ( axi_ethernet_cdc.ar_lock       ),
            .s_axi_arcache  ( axi_ethernet_cdc.ar_cache      ),
            .s_axi_arprot   ( axi_ethernet_cdc.ar_prot       ),
            .s_axi_arregion ( axi_ethernet_cdc.ar_region     ),
            .s_axi_arqos    ( axi_ethernet_cdc.ar_qos        ),
            .s_axi_arvalid  ( axi_ethernet_cdc.ar_valid      ),
            .s_axi_arready  ( axi_ethernet_cdc.ar_ready      ),
            .s_axi_rid      ( axi_ethernet_cdc.r_id          ),
            .s_axi_rdata    ( axi_ethernet_cdc.r_data        ),
            .s_axi_rresp    ( axi_ethernet_cdc.r_resp        ),
            .s_axi_rlast    ( axi_ethernet_cdc.r_last        ),
            .s_axi_rvalid   ( axi_ethernet_cdc.r_valid       ),
            .s_axi_rready   ( axi_ethernet_cdc.r_ready       ),

            .m_axi_awaddr   ( s_axi_eth_awaddr  ),
            .m_axi_awlen    ( s_axi_eth_awlen   ),
            .m_axi_awsize   ( s_axi_eth_awsize  ),
            .m_axi_awburst  ( s_axi_eth_awburst ),
            .m_axi_awlock   (                   ),
            .m_axi_awcache  ( s_axi_eth_awcache ),
            .m_axi_awprot   (                   ),
            .m_axi_awregion (                   ),
            .m_axi_awqos    (                   ),
            .m_axi_awvalid  ( s_axi_eth_awvalid ),
            .m_axi_awready  ( s_axi_eth_awready ),
            .m_axi_wdata    ( s_axi_eth_wdata   ),
            .m_axi_wstrb    ( s_axi_eth_wstrb   ),
            .m_axi_wlast    ( s_axi_eth_wlast   ),
            .m_axi_wvalid   ( s_axi_eth_wvalid  ),
            .m_axi_wready   ( s_axi_eth_wready  ),
            .m_axi_bresp    ( s_axi_eth_bresp   ),
            .m_axi_bvalid   ( s_axi_eth_bvalid  ),
            .m_axi_bready   ( s_axi_eth_bready  ),
            .m_axi_araddr   ( s_axi_eth_araddr  ),
            .m_axi_arlen    ( s_axi_eth_arlen   ),
            .m_axi_arsize   ( s_axi_eth_arsize  ),
            .m_axi_arburst  ( s_axi_eth_arburst ),
            .m_axi_arlock   (                   ),
            .m_axi_arcache  ( s_axi_eth_arcache ),
            .m_axi_arprot   (                   ),
            .m_axi_arregion (                   ),
            .m_axi_arqos    (                   ),
            .m_axi_arvalid  ( s_axi_eth_arvalid ),
            .m_axi_arready  ( s_axi_eth_arready ),
            .m_axi_rdata    ( s_axi_eth_rdata   ),
            .m_axi_rresp    ( s_axi_eth_rresp   ),
            .m_axi_rlast    ( s_axi_eth_rlast   ),
            .m_axi_rvalid   ( s_axi_eth_rvalid  ),
            .m_axi_rready   ( s_axi_eth_rready  )
        );

        logic       phy_rx_clk;
        logic       phy_crs;
        logic       phy_dv;
        logic [3:0] phy_rx_data;
        logic       phy_col;
        logic       phy_rx_er;
        logic       phy_rst_n;
        logic       phy_tx_en;
        logic [3:0] phy_tx_data;
        logic       phy_mdio_i;
        logic       phy_mdio_o;
        logic       phy_mdio_t;
        logic       phy_mdc;

        xlnx_axi_ethernetlite i_xlnx_axi_ethernetlite (
            .s_axi_aclk    ( eth_clk_i              ),
            .s_axi_aresetn ( s_eth_rst_n            ),
            .ip2intc_irpt  ( irq_sources[2]         ),
            .s_axi_awaddr  ( s_axi_eth_awaddr[12:0] ),
            .s_axi_awlen   ( s_axi_eth_awlen        ),
            .s_axi_awsize  ( s_axi_eth_awsize       ),
            .s_axi_awburst ( s_axi_eth_awburst      ),
            .s_axi_awcache ( s_axi_eth_awcache      ),
            .s_axi_awvalid ( s_axi_eth_awvalid      ),
            .s_axi_awready ( s_axi_eth_awready      ),
            .s_axi_wdata   ( s_axi_eth_wdata        ),
            .s_axi_wstrb   ( s_axi_eth_wstrb        ),
            .s_axi_wlast   ( s_axi_eth_wlast        ),
            .s_axi_wvalid  ( s_axi_eth_wvalid       ),
            .s_axi_wready  ( s_axi_eth_wready       ),
            .s_axi_bresp   ( s_axi_eth_bresp        ),
            .s_axi_bvalid  ( s_axi_eth_bvalid       ),
            .s_axi_bready  ( s_axi_eth_bready       ),
            .s_axi_araddr  ( s_axi_eth_araddr[12:0] ),
            .s_axi_arlen   ( s_axi_eth_arlen        ),
            .s_axi_arsize  ( s_axi_eth_arsize       ),
            .s_axi_arburst ( s_axi_eth_arburst      ),
            .s_axi_arcache ( s_axi_eth_arcache      ),
            .s_axi_arvalid ( s_axi_eth_arvalid      ),
            .s_axi_arready ( s_axi_eth_arready      ),
            .s_axi_rdata   ( s_axi_eth_rdata        ),
            .s_axi_rresp   ( s_axi_eth_rresp        ),
            .s_axi_rlast   ( s_axi_eth_rlast        ),
            .s_axi_rvalid  ( s_axi_eth_rvalid       ),
            .s_axi_rready  ( s_axi_eth_rready       ),
            .phy_tx_clk    ( phy_tx_clk_i           ),
            .phy_rx_clk    ( phy_rx_clk             ),
            .phy_crs       ( phy_crs                ),
            .phy_dv        ( phy_dv                 ),
            .phy_rx_data   ( phy_rx_data            ),
            .phy_col       ( phy_col                ),
            .phy_rx_er     ( phy_rx_er              ),
            .phy_rst_n     ( phy_rst_n              ),
            .phy_tx_en     ( phy_tx_en              ),
            .phy_tx_data   ( phy_tx_data            ),
            .phy_mdio_i    ( phy_mdio_i             ),
            .phy_mdio_o    ( phy_mdio_o             ),
            .phy_mdio_t    ( phy_mdio_t             ),
            .phy_mdc       ( phy_mdc                )
        );

        assign phy_crs = 1'b0;
        assign phy_col = 1'b0;

        rgmii_to_mii_conv_xilinx i_rgmii_to_mii_conv_xilinx (
            .rgmii_phy_txc   ( eth_txck     ),
            .rgmii_phy_txctl ( eth_txctl    ),
            .rgmii_phy_txd   ( eth_txd      ),
            .rgmii_phy_rxc   ( eth_rxck     ),
            .rgmii_phy_rxctl ( eth_rxctl    ),
            .rgmii_phy_rxd   ( eth_rxd      ),
            .rgmii_phy_rst_n ( eth_rst_n    ),
            .rgmii_phy_mdio  ( eth_mdio     ),
            .rgmii_phy_mdc   ( eth_mdc      ),
            .mem_clk_i       ( clk_200MHz_i ),
            .net_phy_rst_n   ( phy_rst_n    ),
            .net_phy_tx_clk  ( phy_tx_clk_i ),
            .net_phy_tx_en   ( phy_tx_en    ),
            .net_phy_tx_data ( phy_tx_data  ),
            .net_phy_rx_clk  ( phy_rx_clk   ),
            .net_phy_dv      ( phy_dv       ),
            .net_phy_rx_data ( phy_rx_data  ),
            .net_phy_rx_er   ( phy_rx_er    ),
            .net_mdio_i      ( phy_mdio_o   ),
            .net_mdio_o      ( phy_mdio_i   ),
            .net_mdio_t      ( phy_mdio_t   ),
            .net_phy_mdc     ( phy_mdc      )
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

        logic [31:0] s_axi_gpio_awaddr;
        logic [7:0]  s_axi_gpio_awlen;
        logic [2:0]  s_axi_gpio_awsize;
        logic [1:0]  s_axi_gpio_awburst;
        logic [3:0]  s_axi_gpio_awcache;
        logic        s_axi_gpio_awvalid;
        logic        s_axi_gpio_awready;
        logic [31:0] s_axi_gpio_wdata;
        logic [3:0]  s_axi_gpio_wstrb;
        logic        s_axi_gpio_wlast;
        logic        s_axi_gpio_wvalid;
        logic        s_axi_gpio_wready;
        logic [1:0]  s_axi_gpio_bresp;
        logic        s_axi_gpio_bvalid;
        logic        s_axi_gpio_bready;
        logic [31:0] s_axi_gpio_araddr;
        logic [7:0]  s_axi_gpio_arlen;
        logic [2:0]  s_axi_gpio_arsize;
        logic [1:0]  s_axi_gpio_arburst;
        logic [3:0]  s_axi_gpio_arcache;
        logic        s_axi_gpio_arvalid;
        logic        s_axi_gpio_arready;
        logic [31:0] s_axi_gpio_rdata;
        logic [1:0]  s_axi_gpio_rresp;
        logic        s_axi_gpio_rlast;
        logic        s_axi_gpio_rvalid;
        // system-bus is 64-bit, convert down to 32 bit
        xlnx_axi_dwidth_converter i_xlnx_axi_dwidth_converter_gpio (
            .s_axi_aclk     ( clk_i              ),
            .s_axi_aresetn  ( rst_ni             ),
            .s_axi_awid     ( gpio.aw_id         ),
            .s_axi_awaddr   ( gpio.aw_addr[31:0] ),
            .s_axi_awlen    ( gpio.aw_len        ),
            .s_axi_awsize   ( gpio.aw_size       ),
            .s_axi_awburst  ( gpio.aw_burst      ),
            .s_axi_awlock   ( gpio.aw_lock       ),
            .s_axi_awcache  ( gpio.aw_cache      ),
            .s_axi_awprot   ( gpio.aw_prot       ),
            .s_axi_awregion ( gpio.aw_region     ),
            .s_axi_awqos    ( gpio.aw_qos        ),
            .s_axi_awvalid  ( gpio.aw_valid      ),
            .s_axi_awready  ( gpio.aw_ready      ),
            .s_axi_wdata    ( gpio.w_data        ),
            .s_axi_wstrb    ( gpio.w_strb        ),
            .s_axi_wlast    ( gpio.w_last        ),
            .s_axi_wvalid   ( gpio.w_valid       ),
            .s_axi_wready   ( gpio.w_ready       ),
            .s_axi_bid      ( gpio.b_id          ),
            .s_axi_bresp    ( gpio.b_resp        ),
            .s_axi_bvalid   ( gpio.b_valid       ),
            .s_axi_bready   ( gpio.b_ready       ),
            .s_axi_arid     ( gpio.ar_id         ),
            .s_axi_araddr   ( gpio.ar_addr[31:0] ),
            .s_axi_arlen    ( gpio.ar_len        ),
            .s_axi_arsize   ( gpio.ar_size       ),
            .s_axi_arburst  ( gpio.ar_burst      ),
            .s_axi_arlock   ( gpio.ar_lock       ),
            .s_axi_arcache  ( gpio.ar_cache      ),
            .s_axi_arprot   ( gpio.ar_prot       ),
            .s_axi_arregion ( gpio.ar_region     ),
            .s_axi_arqos    ( gpio.ar_qos        ),
            .s_axi_arvalid  ( gpio.ar_valid      ),
            .s_axi_arready  ( gpio.ar_ready      ),
            .s_axi_rid      ( gpio.r_id          ),
            .s_axi_rdata    ( gpio.r_data        ),
            .s_axi_rresp    ( gpio.r_resp        ),
            .s_axi_rlast    ( gpio.r_last        ),
            .s_axi_rvalid   ( gpio.r_valid       ),
            .s_axi_rready   ( gpio.r_ready       ),

            .m_axi_awaddr   ( s_axi_gpio_awaddr  ),
            .m_axi_awlen    ( s_axi_gpio_awlen   ),
            .m_axi_awsize   ( s_axi_gpio_awsize  ),
            .m_axi_awburst  ( s_axi_gpio_awburst ),
            .m_axi_awlock   (                    ),
            .m_axi_awcache  ( s_axi_gpio_awcache ),
            .m_axi_awprot   (                    ),
            .m_axi_awregion (                    ),
            .m_axi_awqos    (                    ),
            .m_axi_awvalid  ( s_axi_gpio_awvalid ),
            .m_axi_awready  ( s_axi_gpio_awready ),
            .m_axi_wdata    ( s_axi_gpio_wdata   ),
            .m_axi_wstrb    ( s_axi_gpio_wstrb   ),
            .m_axi_wlast    ( s_axi_gpio_wlast   ),
            .m_axi_wvalid   ( s_axi_gpio_wvalid  ),
            .m_axi_wready   ( s_axi_gpio_wready  ),
            .m_axi_bresp    ( s_axi_gpio_bresp   ),
            .m_axi_bvalid   ( s_axi_gpio_bvalid  ),
            .m_axi_bready   ( s_axi_gpio_bready  ),
            .m_axi_araddr   ( s_axi_gpio_araddr  ),
            .m_axi_arlen    ( s_axi_gpio_arlen   ),
            .m_axi_arsize   ( s_axi_gpio_arsize  ),
            .m_axi_arburst  ( s_axi_gpio_arburst ),
            .m_axi_arlock   (                    ),
            .m_axi_arcache  ( s_axi_gpio_arcache ),
            .m_axi_arprot   (                    ),
            .m_axi_arregion (                    ),
            .m_axi_arqos    (                    ),
            .m_axi_arvalid  ( s_axi_gpio_arvalid ),
            .m_axi_arready  ( s_axi_gpio_arready ),
            .m_axi_rdata    ( s_axi_gpio_rdata   ),
            .m_axi_rresp    ( s_axi_gpio_rresp   ),
            .m_axi_rlast    ( s_axi_gpio_rlast   ),
            .m_axi_rvalid   ( s_axi_gpio_rvalid  ),
            .m_axi_rready   ( s_axi_gpio_rready  )
        );

        xlnx_axi_gpio i_xlnx_axi_gpio (
            .s_axi_aclk    ( clk_i                  ),
            .s_axi_aresetn ( rst_ni                 ),
            .s_axi_awaddr  ( s_axi_gpio_awaddr[8:0] ),
            .s_axi_awvalid ( s_axi_gpio_awvalid     ),
            .s_axi_awready ( s_axi_gpio_awready     ),
            .s_axi_wdata   ( s_axi_gpio_wdata       ),
            .s_axi_wstrb   ( s_axi_gpio_wstrb       ),
            .s_axi_wvalid  ( s_axi_gpio_wvalid      ),
            .s_axi_wready  ( s_axi_gpio_wready      ),
            .s_axi_bresp   ( s_axi_gpio_bresp       ),
            .s_axi_bvalid  ( s_axi_gpio_bvalid      ),
            .s_axi_bready  ( s_axi_gpio_bready      ),
            .s_axi_araddr  ( s_axi_gpio_araddr[8:0] ),
            .s_axi_arvalid ( s_axi_gpio_arvalid     ),
            .s_axi_arready ( s_axi_gpio_arready     ),
            .s_axi_rdata   ( s_axi_gpio_rdata       ),
            .s_axi_rresp   ( s_axi_gpio_rresp       ),
            .s_axi_rvalid  ( s_axi_gpio_rvalid      ),
            .s_axi_rready  ( s_axi_gpio_rready      ),
            .gpio_io_i     ( '0                     ),
            .gpio_io_o     ( leds_o                 ),
            .gpio_io_t     (                        ),
            .gpio2_io_i    ( dip_switches_i         )
        );

        assign s_axi_gpio_rlast = 1'b1;
        assign s_axi_gpio_wlast = 1'b1;
    end
endmodule
