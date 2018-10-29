// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Top-level for Genesys 2
module ariane_xilinx (
    input  logic           cpu_resetn,
    input  logic           sys_clk_p,
    input  logic           sys_clk_n,
    inout  logic  [31:0]   ddr3_dq,
    inout  logic  [3:0]    ddr3_dqs_n,
    inout  logic  [3:0]    ddr3_dqs_p,
    output logic  [14:0]   ddr3_addr,
    output logic  [2:0]    ddr3_ba,
    output logic           ddr3_ras_n,
    output logic           ddr3_cas_n,
    output logic           ddr3_we_n,
    output logic           ddr3_reset_n,
    output logic  [0:0]    ddr3_ck_p,
    output logic  [0:0]    ddr3_ck_n,
    output logic  [0:0]    ddr3_cke,
    output logic  [0:0]    ddr3_cs_n,
    output logic  [3:0]    ddr3_dm,
    output logic  [0:0]    ddr3_odt,

    input  logic           tck,
    input  logic           tms,
    input  logic           trst_n,
    input  logic           tdi,
    output logic           tdo,

    input  logic           rx,
    output logic           tx,

    output logic [7:0]     led,
    input  logic [7:0]     sw,
    output logic           fan_pwm,

    // SPI
    output logic           spi_mosi,
    input  logic           spi_miso,
    output logic           spi_ss,
    output logic           spi_clk_o
    //output logic       spi_ip2intc_irtp
);

localparam NBSlave = 4; // debug, Instruction fetch, data bypass, data
localparam CacheStartAddr = (1 << 31);
localparam AxiAddrWidth = 64;
localparam AxiDataWidth = 64;
localparam AxiIdWidthMaster = 2;
localparam AxiIdWidthSlaves = AxiIdWidthMaster + $clog2(NBSlave); // 4
localparam AxiUserWidth = 1;

AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthMaster ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) slave[NBSlave-1:0]();

AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthMaster ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) slave_slice[NBSlave-1:0]();

AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) master[ariane_soc::NB_PERIPHERALS-1:0]();

// disable test-enable
logic test_en;
logic ndmreset;
logic ndmreset_n;
logic debug_req_irq;
logic time_irq;
logic ipi;

logic clk;
logic ddr_sync_reset;
logic ddr_clock_out;

logic rst_n, rst;
logic cpu_reset;

// DDR
logic [3:0]  s_axi_awid;
logic [63:0] s_axi_awaddr;
logic [7:0]  s_axi_awlen;
logic [2:0]  s_axi_awsize;
logic [1:0]  s_axi_awburst;
logic [0:0]  s_axi_awlock;
logic [3:0]  s_axi_awcache;
logic [2:0]  s_axi_awprot;
logic [3:0]  s_axi_awregion;
logic [3:0]  s_axi_awqos;
logic        s_axi_awvalid;
logic        s_axi_awready;
logic [63:0] s_axi_wdata;
logic [7:0]  s_axi_wstrb;
logic        s_axi_wlast;
logic        s_axi_wvalid;
logic        s_axi_wready;
logic [3:0]  s_axi_bid;
logic [1:0]  s_axi_bresp;
logic        s_axi_bvalid;
logic        s_axi_bready;
logic [3:0]  s_axi_arid;
logic [63:0] s_axi_araddr;
logic [7:0]  s_axi_arlen;
logic [2:0]  s_axi_arsize;
logic [1:0]  s_axi_arburst;
logic [0:0]  s_axi_arlock;
logic [3:0]  s_axi_arcache;
logic [2:0]  s_axi_arprot;
logic [3:0]  s_axi_arregion;
logic [3:0]  s_axi_arqos;
logic        s_axi_arvalid;
logic        s_axi_arready;
logic [3:0]  s_axi_rid;
logic [63:0] s_axi_rdata;
logic [1:0]  s_axi_rresp;
logic        s_axi_rlast;
logic        s_axi_rvalid;
logic        s_axi_rready;

// ROM
logic                    rom_req;
logic [AxiAddrWidth-1:0] rom_addr;
logic [AxiDataWidth-1:0] rom_rdata;

// Debug
logic          debug_req_valid;
logic          debug_req_ready;
dm::dmi_req_t  debug_req;
logic          debug_resp_valid;
logic          debug_resp_ready;
dm::dmi_resp_t debug_resp;

logic dmactive;

// UART
logic [3:0]  uart_axi_lite_awaddr;
logic        uart_axi_lite_awvalid;
logic        uart_axi_lite_awready;
logic [31:0] uart_axi_lite_wdata;
logic [3:0]  uart_axi_lite_wstrb;
logic        uart_axi_lite_wvalid;
logic        uart_axi_lite_wready;
logic [1:0]  uart_axi_lite_bresp;
logic        uart_axi_lite_bvalid;
logic        uart_axi_lite_bready;
logic [3:0]  uart_axi_lite_araddr;
logic        uart_axi_lite_arvalid;
logic        uart_axi_lite_arready;
logic [31:0] uart_axi_lite_rdata;
logic [1:0]  uart_axi_lite_rresp;
logic        uart_axi_lite_rvalid;
logic        uart_axi_lite_rready;

// IRQ
logic [1:0] irq;

// Assignments
assign cpu_reset  = ~cpu_resetn;
assign rst_n      = ~ddr_sync_reset;
assign rst        = ddr_sync_reset;
assign test_en    = 1'b0;
assign ndmreset_n = ~ndmreset ;

logic [NBSlave-1:0] pc_asserted;

// Slice the AXI Masters (slave ports on the XBar)
for (genvar i = 0; i < NBSlave; i++) begin : slave_cut_gen
    axi_cut #(
        .ADDR_WIDTH ( AxiAddrWidth     ),
        .DATA_WIDTH ( AxiDataWidth     ),
        .ID_WIDTH   ( AxiIdWidthMaster ),
        .USER_WIDTH ( AxiUserWidth     )
    ) i_axi_cut (
        .clk_i  ( clk            ),
        .rst_ni ( ndmreset_n     ),
        .in     ( slave_slice[i] ),
        .out    ( slave[i]       )
    );

    axi_protocol_checker_0 i_axi_protocol_checker (
      .pc_status( ), // debug probe
      .pc_asserted(pc_asserted[i]),
      .aclk(clk),
      .aresetn(ndmreset_n),
      .pc_axi_awid(slave[i].aw_id),
      .pc_axi_awaddr(slave[i].aw_addr),
      .pc_axi_awlen(slave[i].aw_len),
      .pc_axi_awsize(slave[i].aw_size),
      .pc_axi_awburst(slave[i].aw_burst),
      .pc_axi_awlock(slave[i].aw_lock),
      .pc_axi_awcache(slave[i].aw_cache),
      .pc_axi_awprot(slave[i].aw_prot),
      .pc_axi_awqos(slave[i].aw_qos),
      .pc_axi_awregion(slave[i].aw_region),
      .pc_axi_awready(slave[i].aw_ready),
      .pc_axi_awvalid(slave[i].aw_valid),
      .pc_axi_awuser(slave[i].aw_user),
      .pc_axi_wlast(slave[i].w_last),
      .pc_axi_wdata(slave[i].w_data),
      .pc_axi_wstrb(slave[i].w_strb),
      .pc_axi_wuser(slave[i].w_user),
      .pc_axi_wvalid(slave[i].w_valid),
      .pc_axi_wready(slave[i].w_ready),
      .pc_axi_bid(slave[i].b_id),
      .pc_axi_bresp(slave[i].b_resp),
      .pc_axi_buser(slave[i].b_user),
      .pc_axi_bvalid(slave[i].b_valid),
      .pc_axi_bready(slave[i].b_ready),
      .pc_axi_arid(slave[i].ar_id),
      .pc_axi_araddr(slave[i].ar_addr),
      .pc_axi_arlen(slave[i].ar_len),
      .pc_axi_arsize(slave[i].ar_size),
      .pc_axi_arburst(slave[i].ar_burst),
      .pc_axi_arlock(slave[i].ar_lock),
      .pc_axi_arcache(slave[i].ar_cache),
      .pc_axi_arprot(slave[i].ar_prot),
      .pc_axi_arqos(slave[i].ar_qos),
      .pc_axi_arregion(slave[i].ar_region),
      .pc_axi_aruser(slave[i].ar_user),
      .pc_axi_arvalid(slave[i].ar_valid),
      .pc_axi_arready(slave[i].ar_ready),
      .pc_axi_rid(slave[i].r_id),
      .pc_axi_rlast(slave[i].r_last),
      .pc_axi_rdata(slave[i].r_data),
      .pc_axi_rresp(slave[i].r_resp),
      .pc_axi_ruser(slave[i].r_user),
      .pc_axi_rvalid(slave[i].r_valid),
      .pc_axi_rready(slave[i].r_ready)
    );
end

// ---------------
// AXI Xbar
// ---------------
axi_node_intf_wrap #(
    // three ports from Ariane (instruction, data and bypass)
    .NB_SLAVE       ( NBSlave                    ),
    .NB_MASTER      ( ariane_soc::NB_PERIPHERALS ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth               ),
    .AXI_DATA_WIDTH ( AxiDataWidth               ),
    .AXI_USER_WIDTH ( AxiUserWidth               ),
    .AXI_ID_WIDTH   ( AxiIdWidthMaster           )
) i_axi_xbar (
    .clk          ( clk        ),
    .rst_n        ( ndmreset_n ),
    .test_en_i    ( test_en    ),
    .slave        ( slave      ),
    .master       ( master     ),
    .start_addr_i ({
        ariane_soc::DebugBase,
        ariane_soc::ROMBase,
        ariane_soc::CLINTBase,
        ariane_soc::PLICBase,
        ariane_soc::UARTBase,
        ariane_soc::SPIBase,
        ariane_soc::DRAMBase
    }),
    .end_addr_i   ({
        ariane_soc::DebugBase + ariane_soc::DebugLength,
        ariane_soc::ROMBase   + ariane_soc::ROMLength,
        ariane_soc::CLINTBase + ariane_soc::CLINTLength,
        ariane_soc::PLICBase  + ariane_soc::PLICLength,
        ariane_soc::UARTBase  + ariane_soc::UARTLength,
        ariane_soc::SPIBase   + ariane_soc::SPILength,
        ariane_soc::DRAMBase  + ariane_soc::DRAMLength
    })
);

// ---------------
// Debug Module
// ---------------
dmi_jtag i_dmi_jtag (
    .clk_i                ( clk                  ),
    .rst_ni               ( rst_n                ),
    .dmi_rst_no           (                      ), // keep open
    .dmi_req_valid_o      ( debug_req_valid      ),
    .dmi_req_ready_i      ( debug_req_ready      ),
    .dmi_req_o            ( debug_req            ),
    .dmi_resp_valid_i     ( debug_resp_valid     ),
    .dmi_resp_ready_o     ( debug_resp_ready     ),
    .dmi_resp_i           ( debug_resp           ),
    .tck_i                ( tck    ),
    .tms_i                ( tms    ),
    .trst_ni              ( trst_n ),
    .td_i                 ( tdi    ),
    .td_o                 ( tdo    ),
    .tdo_oe_o             (        )
);

// debug module
dm_top #(
    // current implementation only supports 1 hart
    .NrHarts              ( 1                    ),
    .AxiIdWidth           ( AxiIdWidthSlaves     ),
    .AxiAddrWidth         ( AxiAddrWidth         ),
    .AxiDataWidth         ( AxiDataWidth         ),
    .AxiUserWidth         ( AxiUserWidth         )
) i_dm_top (
    .clk_i                ( clk                        ),
    .rst_ni               ( rst_n                      ), // PoR
    .testmode_i           ( test_en                    ),
    .ndmreset_o           ( ndmreset                   ),
    .dmactive_o           ( dmactive                   ), // active debug session
    .debug_req_o          ( debug_req_irq              ),
    .unavailable_i        ( '0                         ),
    .axi_master           ( slave_slice[3]             ),
    .axi_slave            ( master[ariane_soc::Debug]  ),
    .dmi_rst_ni           ( rst_n                      ),
    .dmi_req_valid_i      ( debug_req_valid            ),
    .dmi_req_ready_o      ( debug_req_ready            ),
    .dmi_req_i            ( debug_req                  ),
    .dmi_resp_valid_o     ( debug_resp_valid           ),
    .dmi_resp_ready_i     ( debug_resp_ready           ),
    .dmi_resp_o           ( debug_resp                 )
);

// ---------------
// Core
// ---------------
ariane #(
    .CACHE_START_ADDR ( CacheStartAddr   ),
    .AXI_ID_WIDTH     ( AxiIdWidthMaster ),
    .AXI_USER_WIDTH   ( AxiUserWidth     )
) i_ariane (
    .clk_i                ( clk                 ),
    .rst_ni               ( ndmreset_n          ),
    .boot_addr_i          ( ariane_soc::ROMBase ), // start fetching from ROM
    .core_id_i            ( '0                  ),
    .cluster_id_i         ( '0                  ),
    .irq_i                ( irq                 ),
    .ipi_i                ( ipi                 ),
    .time_irq_i           ( timer_irq           ),
    .debug_req_i          ( debug_req_irq       ),
    .data_if              ( slave_slice[2]      ),
    .bypass_if            ( slave_slice[1]      ),
    .instr_if             ( slave_slice[0]      )
);

// ---------------
// CLINT
// ---------------
logic rtc;

// divide clock by two
always_ff @(posedge clk or negedge ndmreset_n) begin
  if (~ndmreset_n) begin
    rtc <= 0;
  end else begin
    rtc <= rtc ^ 1'b1;
  end
end

clint #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .NR_CORES       ( 1                )
) i_clint (
    .clk_i       ( clk                       ),
    .rst_ni      ( ndmreset_n                ),
    .slave       ( master[ariane_soc::CLINT] ),
    .rtc_i       ( rtc                       ),
    .timer_irq_o ( timer_irq                 ),
    .ipi_o       ( ipi                       )
);

// ---------------
// ROM
// ---------------
axi2mem #(
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) i_axi2rom (
    .clk_i  ( clk                     ),
    .rst_ni ( ndmreset_n              ),
    .slave  ( master[ariane_soc::ROM] ),
    .req_o  ( rom_req                 ),
    .we_o   (                         ),
    .addr_o ( rom_addr                ),
    .be_o   (                         ),
    .data_o (                         ),
    .data_i ( rom_rdata               )
);

bootrom i_bootrom (
    .clk_i      ( clk       ),
    .req_i      ( rom_req   ),
    .addr_i     ( rom_addr  ),
    .rdata_o    ( rom_rdata )
);

// ---------------
// Peripherals
// ---------------
ariane_peripherals #(
    .AxiAddrWidth(AxiAddrWidth),
    .AxiDataWidth(AxiDataWidth)
) i_ariane_peripherals (
    .clk_i           (clk                     ),
    .rst_ni          (ndmreset_n              ),
    .plic            (master[ariane_soc::PLIC]),
    .uart            (master[ariane_soc::UART]),
    .spi             (master[ariane_soc::SPI] ),
    .irq_o           (irq                     ),
    .rx_i            (rx                      ),
    .tx_o            (tx                      ),
    .spi_clk_o       (spi_clk_o               ),
    .spi_mosi        (spi_mosi                ),
    .spi_miso        (spi_miso                ),
    .spi_ss          (spi_ss                  ),
    .spi_ip2intc_irtp(                        )
);

// ---------------------
// Board peripherals
// ---------------------
fan_ctrl i_fan_ctrl (
    .clk_i         ( clk        ),
    .rst_ni        ( ndmreset_n ),
    .pwm_setting_i ( sw[3:0]    ),
    .fan_pwm_o     ( fan_pwm    )
);

ariane_leds i_ariane_leds (
  .clk_i          ( clk          ),
  .rst_ni         ( rst_n        ),
  .led_o          ( led          ),
  .pc_asserted_i  ( pc_asserted  ),
  .dmactive_i     ( dmactive     ),
  .commit_valid_i ( '0           )
);

clk_wiz_0 i_clk_gen (
  .clk_out1 ( clk           ),
  .reset    ( cpu_reset     ),
  .locked   (               ), // keep open
  .clk_in1  ( ddr_clock_out )
);

// ---------------
// DDR
// ---------------
assign master[ariane_soc::DRAM].r_user = '0;
assign master[ariane_soc::DRAM].b_user = '0;

// DDR 4 Subsystem
axi_clock_converter_0 axi_clock_converter (
  .s_axi_aclk(clk),
  .s_axi_aresetn(ndmreset_n),
  .s_axi_awid(master[ariane_soc::DRAM].aw_id),
  .s_axi_awaddr(master[ariane_soc::DRAM].aw_addr),
  .s_axi_awlen(master[ariane_soc::DRAM].aw_len),
  .s_axi_awsize(master[ariane_soc::DRAM].aw_size),
  .s_axi_awburst(master[ariane_soc::DRAM].aw_burst),
  .s_axi_awlock(master[ariane_soc::DRAM].aw_lock),
  .s_axi_awcache(master[ariane_soc::DRAM].aw_cache),
  .s_axi_awprot(master[ariane_soc::DRAM].aw_prot),
  .s_axi_awregion(master[ariane_soc::DRAM].aw_region),
  .s_axi_awqos(master[ariane_soc::DRAM].aw_qos),
  .s_axi_awvalid(master[ariane_soc::DRAM].aw_valid),
  .s_axi_awready(master[ariane_soc::DRAM].aw_ready),
  .s_axi_wdata(master[ariane_soc::DRAM].w_data),
  .s_axi_wstrb(master[ariane_soc::DRAM].w_strb),
  .s_axi_wlast(master[ariane_soc::DRAM].w_last),
  .s_axi_wvalid(master[ariane_soc::DRAM].w_valid),
  .s_axi_wready(master[ariane_soc::DRAM].w_ready),
  .s_axi_bid(master[ariane_soc::DRAM].b_id),
  .s_axi_bresp(master[ariane_soc::DRAM].b_resp),
  .s_axi_bvalid(master[ariane_soc::DRAM].b_valid),
  .s_axi_bready(master[ariane_soc::DRAM].b_ready),
  .s_axi_arid(master[ariane_soc::DRAM].ar_id),
  .s_axi_araddr(master[ariane_soc::DRAM].ar_addr),
  .s_axi_arlen(master[ariane_soc::DRAM].ar_len),
  .s_axi_arsize(master[ariane_soc::DRAM].ar_size),
  .s_axi_arburst(master[ariane_soc::DRAM].ar_burst),
  .s_axi_arlock(master[ariane_soc::DRAM].ar_lock),
  .s_axi_arcache(master[ariane_soc::DRAM].ar_cache),
  .s_axi_arprot(master[ariane_soc::DRAM].ar_prot),
  .s_axi_arregion(master[ariane_soc::DRAM].ar_region),
  .s_axi_arqos(master[ariane_soc::DRAM].ar_qos),
  .s_axi_arvalid(master[ariane_soc::DRAM].ar_valid),
  .s_axi_arready(master[ariane_soc::DRAM].ar_ready),
  .s_axi_rid(master[ariane_soc::DRAM].r_id),
  .s_axi_rdata(master[ariane_soc::DRAM].r_data),
  .s_axi_rresp(master[ariane_soc::DRAM].r_resp),
  .s_axi_rlast(master[ariane_soc::DRAM].r_last),
  .s_axi_rvalid(master[ariane_soc::DRAM].r_valid),
  .s_axi_rready(master[ariane_soc::DRAM].r_ready),
  // to size converter
  .m_axi_aclk(ddr_clock_out),
  .m_axi_aresetn(ndmreset_n),
  .m_axi_awid(s_axi_awid),
  .m_axi_awaddr(s_axi_awaddr),
  .m_axi_awlen(s_axi_awlen),
  .m_axi_awsize(s_axi_awsize),
  .m_axi_awburst(s_axi_awburst),
  .m_axi_awlock(s_axi_awlock),
  .m_axi_awcache(s_axi_awcache),
  .m_axi_awprot(s_axi_awprot),
  .m_axi_awregion(s_axi_awregion),
  .m_axi_awqos(s_axi_awqos),
  .m_axi_awvalid(s_axi_awvalid),
  .m_axi_awready(s_axi_awready),
  .m_axi_wdata(s_axi_wdata),
  .m_axi_wstrb(s_axi_wstrb),
  .m_axi_wlast(s_axi_wlast),
  .m_axi_wvalid(s_axi_wvalid),
  .m_axi_wready(s_axi_wready),
  .m_axi_bid(s_axi_bid),
  .m_axi_bresp(s_axi_bresp),
  .m_axi_bvalid(s_axi_bvalid),
  .m_axi_bready(s_axi_bready),
  .m_axi_arid(s_axi_arid),
  .m_axi_araddr(s_axi_araddr),
  .m_axi_arlen(s_axi_arlen),
  .m_axi_arsize(s_axi_arsize),
  .m_axi_arburst(s_axi_arburst),
  .m_axi_arlock(s_axi_arlock),
  .m_axi_arcache(s_axi_arcache),
  .m_axi_arprot(s_axi_arprot),
  .m_axi_arregion(s_axi_arregion),
  .m_axi_arqos(s_axi_arqos),
  .m_axi_arvalid(s_axi_arvalid),
  .m_axi_arready(s_axi_arready),
  .m_axi_rid(s_axi_rid),
  .m_axi_rdata(s_axi_rdata),
  .m_axi_rresp(s_axi_rresp),
  .m_axi_rlast(s_axi_rlast),
  .m_axi_rvalid(s_axi_rvalid),
  .m_axi_rready(s_axi_rready)
);

mig_7series_0 i_ddr (
    .sys_clk_p,
    .sys_clk_n,
    .ddr3_dq,
    .ddr3_dqs_n,
    .ddr3_dqs_p,
    .ddr3_addr,
    .ddr3_ba,
    .ddr3_ras_n,
    .ddr3_cas_n,
    .ddr3_we_n,
    .ddr3_reset_n,
    .ddr3_ck_p,
    .ddr3_ck_n,
    .ddr3_cke,
    .ddr3_cs_n,
    .ddr3_dm,
    .ddr3_odt,
    .mmcm_locked     (                ), // keep open
    .app_sr_req      ( '0             ),
    .app_ref_req     ( '0             ),
    .app_zq_req      ( '0             ),
    .app_sr_active   (                ), // keep open
    .app_ref_ack     (                ), // keep open
    .app_zq_ack      (                ), // keep open
    .ui_clk          ( ddr_clock_out  ),
    .ui_clk_sync_rst ( ddr_sync_reset ),
    .aresetn         ( ndmreset_n     ),
    .s_axi_awid,
    .s_axi_awaddr    ( s_axi_awaddr[29:0] ),
    .s_axi_awlen,
    .s_axi_awsize,
    .s_axi_awburst,
    .s_axi_awlock,
    .s_axi_awcache,
    .s_axi_awprot,
    .s_axi_awqos,
    .s_axi_awvalid,
    .s_axi_awready,
    .s_axi_wdata,
    .s_axi_wstrb,
    .s_axi_wlast,
    .s_axi_wvalid,
    .s_axi_wready,
    .s_axi_bready,
    .s_axi_bid,
    .s_axi_bresp,
    .s_axi_bvalid,
    .s_axi_arid,
    .s_axi_araddr     ( s_axi_araddr[29:0] ),
    .s_axi_arlen,
    .s_axi_arsize,
    .s_axi_arburst,
    .s_axi_arlock,
    .s_axi_arcache,
    .s_axi_arprot,
    .s_axi_arqos,
    .s_axi_arvalid,
    .s_axi_arready,
    .s_axi_rready,
    .s_axi_rid,
    .s_axi_rdata,
    .s_axi_rresp,
    .s_axi_rlast,
    .s_axi_rvalid,
    .init_calib_complete (            ), // keep open
    .device_temp         (            ), // keep open
    .sys_rst             ( cpu_resetn )
);

endmodule