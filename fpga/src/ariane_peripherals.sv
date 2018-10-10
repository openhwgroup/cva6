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
        .clk_i              ( clk                    ),
        .rst_ni             ( ndmreset_n             ),
        .irq_sources_i      ( irq_sources            ),
        .eip_targets_o      ( irq_o                  ),
        .external_bus_io    ( reg_bus                )
    );

    // ---------------
    // UART
    // ---------------
    logic [31:0] s_axi_uart_awaddr;
    logic [7:0]  s_axi_uart_awlen;
    logic [2:0]  s_axi_uart_awsize;
    logic [1:0]  s_axi_uart_awburst;
    logic [0:0]  s_axi_uart_awlock;
    logic [3:0]  s_axi_uart_awcache;
    logic [2:0]  s_axi_uart_awprot;
    logic [3:0]  s_axi_uart_awregion;
    logic [3:0]  s_axi_uart_awqos;
    logic        s_axi_uart_awvalid;
    logic        s_axi_uart_awready;
    logic [31:0] s_axi_uart_wdata;
    logic [3:0]  s_axi_uart_wstrb;
    logic        s_axi_uart_wlast;
    logic        s_axi_uart_wvalid;
    logic        s_axi_uart_wready;
    logic [1:0]  s_axi_uart_bresp;
    logic        s_axi_uart_bvalid;
    logic        s_axi_uart_bready;
    logic [31:0] s_axi_uart_araddr;
    logic [7:0]  s_axi_uart_arlen;
    logic [2:0]  s_axi_uart_arsize;
    logic [1:0]  s_axi_uart_arburst;
    logic [0:0]  s_axi_uart_arlock;
    logic [3:0]  s_axi_uart_arcache;
    logic [2:0]  s_axi_uart_arprot;
    logic [3:0]  s_axi_uart_arregion;
    logic [3:0]  s_axi_uart_arqos;
    logic        s_axi_uart_arvalid;
    logic        s_axi_uart_arready;
    logic [31:0] s_axi_uart_rdata;
    logic [1:0]  s_axi_uart_rresp;
    logic        s_axi_uart_rlast;
    logic        s_axi_uart_rvalid;
    logic        s_axi_uart_rready;

    logic [31:0] m_axi_uart_awaddr;
    logic        m_axi_uart_awvalid;
    logic        m_axi_uart_awready;
    logic [31:0] m_axi_uart_wdata;
    logic [3:0]  m_axi_uart_wstrb;
    logic        m_axi_uart_wvalid;
    logic        m_axi_uart_wready;
    logic [1:0]  m_axi_uart_bresp;
    logic        m_axi_uart_bvalid;
    logic        m_axi_uart_bready;
    logic [31:0] m_axi_uart_araddr;
    logic        m_axi_uart_arvalid;
    logic        m_axi_uart_arready;
    logic [31:0] m_axi_uart_rdata;
    logic [1:0]  m_axi_uart_rresp;
    logic        m_axi_uart_rvalid;
    logic        m_axi_uart_rready;

    axi_dwidth_converter_0 i_axi_dwidth_converter (
        .s_axi_aclk     ( clk_i               ),
        .s_axi_aresetn  ( rst_ni              ),

        .s_axi_awid     ( uart.aw_id          ),
        .s_axi_awaddr   ( uart.aw_addr[31:0]  ),
        .s_axi_awlen    ( uart.aw_len         ),
        .s_axi_awsize   ( uart.aw_size        ),
        .s_axi_awburst  ( uart.aw_burst       ),
        .s_axi_awlock   ( uart.aw_lock        ),
        .s_axi_awcache  ( uart.aw_cache       ),
        .s_axi_awprot   ( uart.aw_prot        ),
        .s_axi_awregion ( uart.aw_region      ),
        .s_axi_awqos    ( uart.aw_qos         ),
        .s_axi_awvalid  ( uart.aw_valid       ),
        .s_axi_awready  ( uart.aw_ready       ),
        .s_axi_wdata    ( uart.w_data         ),
        .s_axi_wstrb    ( uart.w_strb         ),
        .s_axi_wlast    ( uart.w_last         ),
        .s_axi_wvalid   ( uart.w_valid        ),
        .s_axi_wready   ( uart.w_ready        ),
        .s_axi_bid      ( uart.b_id           ),
        .s_axi_bresp    ( uart.b_resp         ),
        .s_axi_bvalid   ( uart.b_valid        ),
        .s_axi_bready   ( uart.b_ready        ),
        .s_axi_arid     ( uart.ar_id          ),
        .s_axi_araddr   ( uart.ar_addr[31:0]  ),
        .s_axi_arlen    ( uart.ar_len         ),
        .s_axi_arsize   ( uart.ar_size        ),
        .s_axi_arburst  ( uart.ar_burst       ),
        .s_axi_arlock   ( uart.ar_lock        ),
        .s_axi_arcache  ( uart.ar_cache       ),
        .s_axi_arprot   ( uart.ar_prot        ),
        .s_axi_arregion ( uart.ar_region      ),
        .s_axi_arqos    ( uart.ar_qos         ),
        .s_axi_arvalid  ( uart.ar_valid       ),
        .s_axi_arready  ( uart.ar_ready       ),
        .s_axi_rid      ( uart.r_id           ),
        .s_axi_rdata    ( uart.r_data         ),
        .s_axi_rresp    ( uart.r_resp         ),
        .s_axi_rlast    ( uart.r_last         ),
        .s_axi_rvalid   ( uart.r_valid        ),
        .s_axi_rready   ( uart.r_ready        ),

        .m_axi_awaddr   ( s_axi_uart_awaddr   ),
        .m_axi_awlen    ( s_axi_uart_awlen    ),
        .m_axi_awsize   ( s_axi_uart_awsize   ),
        .m_axi_awburst  ( s_axi_uart_awburst  ),
        .m_axi_awlock   ( s_axi_uart_awlock   ),
        .m_axi_awcache  ( s_axi_uart_awcache  ),
        .m_axi_awprot   ( s_axi_uart_awprot   ),
        .m_axi_awregion ( s_axi_uart_awregion ),
        .m_axi_awqos    ( s_axi_uart_awqos    ),
        .m_axi_awvalid  ( s_axi_uart_awvalid  ),
        .m_axi_awready  ( s_axi_uart_awready  ),
        .m_axi_wdata    ( s_axi_uart_wdata    ),
        .m_axi_wstrb    ( s_axi_uart_wstrb    ),
        .m_axi_wlast    ( s_axi_uart_wlast    ),
        .m_axi_wvalid   ( s_axi_uart_wvalid   ),
        .m_axi_wready   ( s_axi_uart_wready   ),
        .m_axi_bresp    ( s_axi_uart_bresp    ),
        .m_axi_bvalid   ( s_axi_uart_bvalid   ),
        .m_axi_bready   ( s_axi_uart_bready   ),
        .m_axi_araddr   ( s_axi_uart_araddr   ),
        .m_axi_arlen    ( s_axi_uart_arlen    ),
        .m_axi_arsize   ( s_axi_uart_arsize   ),
        .m_axi_arburst  ( s_axi_uart_arburst  ),
        .m_axi_arlock   ( s_axi_uart_arlock   ),
        .m_axi_arcache  ( s_axi_uart_arcache  ),
        .m_axi_arprot   ( s_axi_uart_arprot   ),
        .m_axi_arregion ( s_axi_uart_arregion ),
        .m_axi_arqos    ( s_axi_uart_arqos    ),
        .m_axi_arvalid  ( s_axi_uart_arvalid  ),
        .m_axi_arready  ( s_axi_uart_arready  ),
        .m_axi_rdata    ( s_axi_uart_rdata    ),
        .m_axi_rresp    ( s_axi_uart_rresp    ),
        .m_axi_rlast    ( s_axi_uart_rlast    ),
        .m_axi_rvalid   ( s_axi_uart_rvalid   ),
        .m_axi_rready   ( s_axi_uart_rready   )
    );

    axi_protocol_converter_0 i_axi_to_axi_lite (
        .aclk           ( clk_i               ),
        .aresetn        ( rst_ni              ),

        .s_axi_awaddr   ( s_axi_uart_awaddr   ),
        .s_axi_awlen    ( s_axi_uart_awlen    ),
        .s_axi_awsize   ( s_axi_uart_awsize   ),
        .s_axi_awburst  ( s_axi_uart_awburst  ),
        .s_axi_awlock   ( s_axi_uart_awlock   ),
        .s_axi_awcache  ( s_axi_uart_awcache  ),
        .s_axi_awprot   ( s_axi_uart_awprot   ),
        .s_axi_awregion ( s_axi_uart_awregion ),
        .s_axi_awqos    ( s_axi_uart_awqos    ),
        .s_axi_awvalid  ( s_axi_uart_awvalid  ),
        .s_axi_awready  ( s_axi_uart_awready  ),
        .s_axi_wdata    ( s_axi_uart_wdata    ),
        .s_axi_wstrb    ( s_axi_uart_wstrb    ),
        .s_axi_wlast    ( s_axi_uart_wlast    ),
        .s_axi_wvalid   ( s_axi_uart_wvalid   ),
        .s_axi_wready   ( s_axi_uart_wready   ),
        .s_axi_bresp    ( s_axi_uart_bresp    ),
        .s_axi_bvalid   ( s_axi_uart_bvalid   ),
        .s_axi_bready   ( s_axi_uart_bready   ),
        .s_axi_araddr   ( s_axi_uart_araddr   ),
        .s_axi_arlen    ( s_axi_uart_arlen    ),
        .s_axi_arsize   ( s_axi_uart_arsize   ),
        .s_axi_arburst  ( s_axi_uart_arburst  ),
        .s_axi_arlock   ( s_axi_uart_arlock   ),
        .s_axi_arcache  ( s_axi_uart_arcache  ),
        .s_axi_arprot   ( s_axi_uart_arprot   ),
        .s_axi_arregion ( s_axi_uart_arregion ),
        .s_axi_arqos    ( s_axi_uart_arqos    ),
        .s_axi_arvalid  ( s_axi_uart_arvalid  ),
        .s_axi_arready  ( s_axi_uart_arready  ),
        .s_axi_rdata    ( s_axi_uart_rdata    ),
        .s_axi_rresp    ( s_axi_uart_rresp    ),
        .s_axi_rlast    ( s_axi_uart_rlast    ),
        .s_axi_rvalid   ( s_axi_uart_rvalid   ),
        .s_axi_rready   ( s_axi_uart_rready   ),

        .m_axi_awaddr   ( m_axi_uart_awaddr   ),
        .m_axi_awprot   (                     ),
        .m_axi_awvalid  ( m_axi_uart_awvalid  ),
        .m_axi_awready  ( m_axi_uart_awready  ),
        .m_axi_wdata    ( m_axi_uart_wdata    ),
        .m_axi_wstrb    ( m_axi_uart_wstrb    ),
        .m_axi_wvalid   ( m_axi_uart_wvalid   ),
        .m_axi_wready   ( m_axi_uart_wready   ),
        .m_axi_bresp    ( m_axi_uart_bresp    ),
        .m_axi_bvalid   ( m_axi_uart_bvalid   ),
        .m_axi_bready   ( m_axi_uart_bready   ),
        .m_axi_araddr   ( m_axi_uart_araddr   ),
        .m_axi_arprot   (                     ),
        .m_axi_arvalid  ( m_axi_uart_arvalid  ),
        .m_axi_arready  ( m_axi_uart_arready  ),
        .m_axi_rdata    ( m_axi_uart_rdata    ),
        .m_axi_rresp    ( m_axi_uart_rresp    ),
        .m_axi_rvalid   ( m_axi_uart_rvalid   ),
        .m_axi_rready   ( m_axi_uart_rready   )
    );

    axi_uartlite_1 i_axi_uart (
        .s_axi_aclk    ( clk_i                  ),
        .s_axi_aresetn ( rst_ni                 ),
        .interrupt     ( irq_sources[0]         ),
        .s_axi_awaddr  ( m_axi_uart_awaddr[3:0] ),
        .s_axi_awvalid ( m_axi_uart_awvalid     ),
        .s_axi_awready ( m_axi_uart_awready     ),
        .s_axi_wdata   ( m_axi_uart_wdata       ),
        .s_axi_wstrb   ( m_axi_uart_wstrb       ),
        .s_axi_wvalid  ( m_axi_uart_wvalid      ),
        .s_axi_wready  ( m_axi_uart_wready      ),
        .s_axi_bresp   ( m_axi_uart_bresp       ),
        .s_axi_bvalid  ( m_axi_uart_bvalid      ),
        .s_axi_bready  ( m_axi_uart_bready      ),
        .s_axi_araddr  ( m_axi_uart_araddr[3:0] ),
        .s_axi_arvalid ( m_axi_uart_arvalid     ),
        .s_axi_arready ( m_axi_uart_arready     ),
        .s_axi_rdata   ( m_axi_uart_rdata       ),
        .s_axi_rresp   ( m_axi_uart_rresp       ),
        .s_axi_rvalid  ( m_axi_uart_rvalid      ),
        .s_axi_rready  ( m_axi_uart_rready      ),
        .rx            ( rx_i                   ),
        .tx            ( tx_o                   )
    );



endmodule