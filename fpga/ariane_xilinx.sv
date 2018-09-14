// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Top-level for ZCU102
module ariane_xilinx (
    input  logic        c0_sys_clk_p,    // Clock
    input  logic        c0_sys_clk_n,    // Clock
    input  logic        sys_rst,         // active high reset
    output logic        c0_ddr4_act_n,
    output logic [16:0] c0_ddr4_adr,
    output logic [1:0]  c0_ddr4_ba,
    output logic [0:0]  c0_ddr4_bg,
    output logic [0:0]  c0_ddr4_cke,
    output logic [0:0]  c0_ddr4_odt,
    output logic [0:0]  c0_ddr4_cs_n,
    output logic [0:0]  c0_ddr4_ck_t,
    output logic [0:0]  c0_ddr4_ck_c,
    output logic        c0_ddr4_reset_n,
    inout  logic [1:0]  c0_ddr4_dm_dbi_n,
    inout  logic [15:0] c0_ddr4_dq,
    inout  logic [1:0]  c0_ddr4_dqs_c,
    inout  logic [1:0]  c0_ddr4_dqs_t,
    input  logic tck,
    input  logic tms,
    input  logic trst_n,
    input  logic tdi,
    output logic tdo
);

localparam logic [63:0] RomBase = 64'h10000;
localparam NBSlave = 4; // debug, Instruction fetch, data bypass, data
localparam NBMaster = 3; // debug, ROM, RAM

localparam logic [63:0] CacheStartAddr = 64'h8000_0000;
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
) master[NBMaster-1:0]();

// disable test-enable
logic test_en;
logic ndmreset;
logic ndmreset_n;
logic debug_req_irq;
logic time_irq;
logic ipi;

logic clk;
logic rst_n;

// DDR
logic c0_ddr4_ui_clk;
logic c0_init_calib_complete; // left open
logic c0_ddr4_ui_clk_sync_rst;
logic addn_ui_clkout1;

logic [3:0] s_axi_awid;
logic [31:0] s_axi_awaddr;
logic [7:0] s_axi_awlen;
logic [2:0] s_axi_awsize;
logic [1:0] s_axi_awburst;
logic [0:0] s_axi_awlock;
logic [3:0] s_axi_awcache;
logic [2:0] s_axi_awprot;
logic [3:0] s_axi_awregion;
logic [3:0] s_axi_awqos;
logic s_axi_awvalid;
logic s_axi_awready;
logic [63:0] s_axi_wdata;
logic [7:0] s_axi_wstrb;
logic s_axi_wlast;
logic s_axi_wvalid;
logic s_axi_wready;
logic [3:0] s_axi_bid;
logic [1:0] s_axi_bresp;
logic s_axi_bvalid;
logic s_axi_bready;
logic [3:0] s_axi_arid;
logic [31:0] s_axi_araddr;
logic [7:0] s_axi_arlen;
logic [2:0] s_axi_arsize;
logic [1:0] s_axi_arburst;
logic [0:0] s_axi_arlock;
logic [3:0] s_axi_arcache;
logic [2:0] s_axi_arprot;
logic [3:0] s_axi_arregion;
logic [3:0] s_axi_arqos;
logic s_axi_arvalid;
logic s_axi_arready;
logic [3:0] s_axi_rid;
logic [63:0] s_axi_rdata;
logic [1:0] s_axi_rresp;
logic s_axi_rlast;
logic s_axi_rvalid;
logic s_axi_rready;

logic [31:0] m_axi_awaddr;
logic [7:0] m_axi_awlen;
logic [2:0] m_axi_awsize;
logic [1:0] m_axi_awburst;
logic [0:0] m_axi_awlock;
logic [3:0] m_axi_awcache;
logic [2:0] m_axi_awprot;
logic [3:0] m_axi_awregion;
logic [3:0] m_axi_awqos;
logic m_axi_awvalid;
logic m_axi_awready;
logic [127:0] m_axi_wdata;
logic [15:0] m_axi_wstrb;
logic m_axi_wlast;
logic m_axi_wvalid;
logic m_axi_wready;
logic [1:0] m_axi_bresp;
logic m_axi_bvalid;
logic m_axi_bready;
logic [31:0] m_axi_araddr;
logic [7:0] m_axi_arlen;
logic [2:0] m_axi_arsize;
logic [1:0] m_axi_arburst;
logic [0:0] m_axi_arlock;
logic [3:0] m_axi_arcache;
logic [2:0] m_axi_arprot;
logic [3:0] m_axi_arregion;
logic [3:0] m_axi_arqos;
logic m_axi_arvalid;
logic m_axi_arready;
logic [127:0] m_axi_rdata;
logic [1:0] m_axi_rresp;
logic m_axi_rlast;
logic m_axi_rvalid;
logic m_axi_rready;

logic        debug_req_valid;
logic        debug_req_ready;
logic [6:0]  debug_req_bits_addr;
logic [1:0]  debug_req_bits_op;
logic [31:0] debug_req_bits_data;
logic        debug_resp_valid;
logic        debug_resp_ready;
logic [1:0]  debug_resp_bits_resp;
logic [31:0] debug_resp_bits_data;

assign clk = addn_ui_clkout1;
assign rst_n = ~c0_ddr4_ui_clk_sync_rst;
assign test_en = 1'b0;
assign ndmreset_n = ~ndmreset ;

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
end

// ---------------
// AXI Xbar
// ---------------
axi_node_intf_wrap #(
    // three ports from Ariane (instruction, data and bypass)
    .NB_SLAVE       ( NBSlave          ),
    .NB_MASTER      ( NBMaster         ), // debug unit, memory unit
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_USER_WIDTH ( AxiUserWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthMaster )
) i_axi_xbar (
    .clk          ( clk                                                                ),
    .rst_n        ( ndmreset_n                                                         ),
    .test_en_i    ( test_en                                                            ),
    .slave        ( slave                                                              ),
    .master       ( master                                                             ),
    .start_addr_i ( {64'h0,   RomBase,            64'h2000000, CacheStartAddr}         ),
    .end_addr_i   ( {64'hFFF, RomBase + 64'hFFFF, 64'h2FFFFFF, CacheStartAddr + 2**24} )
);

dm::dmi_req_t debug_req;;
dm::dmi_resp_t debug_resp;

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
    .clk_i                ( clk                  ),
    .rst_ni               ( rst_n                ), // PoR
    .testmode_i           ( test_en              ),
    .ndmreset_o           ( ndmreset             ),
    .dmactive_o           (                      ), // active debug session
    .debug_req_o          ( debug_req_irq        ),
    .unavailable_i        ( '0                   ),
    .axi_master           ( slave_slice[3]       ),
    .axi_slave            ( master[3]            ),
    .dmi_rst_ni           ( rst_n                ),
    .dmi_req_valid_i      ( debug_req_valid      ),
    .dmi_req_ready_o      ( debug_req_ready      ),
    .dmi_req_i            ( debug_req            ),
    .dmi_resp_valid_o     ( debug_resp_valid     ),
    .dmi_resp_ready_i     ( debug_resp_ready     ),
    .dmi_resp_o           ( debug_resp           )
);

// ---------------
// Core
// ---------------
ariane #(
    .CACHE_START_ADDR ( CacheStartAddr   ),
    .AXI_ID_WIDTH     ( AxiIdWidthMaster ),
    .AXI_USER_WIDTH   ( AxiUserWidth     )
) i_ariane (
    .clk_i                ( clk            ),
    .rst_ni               ( ndmreset_n     ),
    .boot_addr_i          ( RomBase        ), // start fetching from ROM
    .core_id_i            ( '0             ),
    .cluster_id_i         ( '0             ),
    // TODO(zarubaf) Instantiate PLIC
    .irq_i                ( '0             ),
    .ipi_i                ( ipi            ),
    .time_irq_i           ( time_irq       ),
    .debug_req_i          ( debug_req_irq  ),
    .data_if              ( slave_slice[2] ),
    .bypass_if            ( slave_slice[1] ),
    .instr_if             ( slave_slice[0] )
);

// ---------------
// CLINT
// ---------------
clint #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH_SLAVES ),
    .NR_CORES       ( 1                   )
) i_clint (
    .clk_i       ( clk_i     ),
    .rst_ni      ( rst_ni    ),
    .slave       ( master[1] ),
    // TODO(zarubaf): Fix RTC
    .rtc_i       ( 1'b0      ),
    .timer_irq_o ( timer_irq ),
    .ipi_o       ( ipi       )
);

// ---------------
// ROM
// ---------------
logic                    rom_req;
logic [AxiAddrWidth-1:0] rom_addr;
logic [AxiDataWidth-1:0] rom_rdata;

axi2mem #(
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) i_axi2rom (
    .clk_i  ( clk        ),
    .rst_ni ( ndmreset_n ),
    .slave  ( master[2]  ),
    .req_o  ( rom_req    ),
    .we_o   (            ),
    .addr_o ( rom_addr   ),
    .be_o   (            ),
    .data_o (            ),
    .data_i ( rom_rdata  )
);

bootrom i_bootrom (
    .clk_i      ( clk       ),
    .req_i      ( rom_req   ),
    .addr_i     ( rom_addr  ),
    .rdata_o    ( rom_rdata )
);


// DDR 4 Subsystem
axi_clock_converter_0 axi_clock_converter (
  .s_axi_aclk(clk),
  .s_axi_aresetn(ndmreset_n),
  .s_axi_awid(master[0].aw_id),
  .s_axi_awaddr(master[0].aw_addr),
  .s_axi_awlen(master[0].aw_len),
  .s_axi_awsize(master[0].aw_size),
  .s_axi_awburst(master[0].aw_burst),
  .s_axi_awlock(master[0].aw_lock),
  .s_axi_awcache(master[0].aw_cache),
  .s_axi_awprot(master[0].aw_prot),
  .s_axi_awregion(master[0].aw_region),
  .s_axi_awqos(master[0].aw_qos),
  .s_axi_awvalid(master[0].aw_valid),
  .s_axi_awready(master[0].aw_ready),
  .s_axi_wdata(master[0].w_data),
  .s_axi_wstrb(master[0].w_strb),
  .s_axi_wlast(master[0].w_last),
  .s_axi_wvalid(master[0].w_valid),
  .s_axi_wready(master[0].w_ready),
  .s_axi_bid(master[0].b_id),
  .s_axi_bresp(master[0].b_resp),
  .s_axi_bvalid(master[0].b_valid),
  .s_axi_bready(master[0].b_ready),
  .s_axi_arid(master[0].ar_id),
  .s_axi_araddr(master[0].ar_addr[31:0]),
  .s_axi_arlen(master[0].ar_len),
  .s_axi_arsize(master[0].ar_size),
  .s_axi_arburst(master[0].ar_burst),
  .s_axi_arlock(master[0].ar_lock),
  .s_axi_arcache(master[0].ar_cache),
  .s_axi_arprot(master[0].ar_prot),
  .s_axi_arregion(master[0].ar_region),
  .s_axi_arqos(master[0].ar_qos),
  .s_axi_arvalid(master[0].ar_valid),
  .s_axi_arready(master[0].ar_ready),
  .s_axi_rid(master[0].r_id),
  .s_axi_rdata(master[0].r_data),
  .s_axi_rresp(master[0].r_resp),
  .s_axi_rlast(master[0].r_last),
  .s_axi_rvalid(master[0].r_valid),
  .s_axi_rready(master[0].r_ready),
  // to size converter
  .m_axi_aclk(c0_ddr4_ui_clk),
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

axi_dwidth_converter_0 axi_size_converter (
    .s_axi_aclk(c0_ddr4_ui_clk),
    .s_axi_aresetn(ndmreset_n),
    .s_axi_awid,
    .s_axi_awaddr,
    .s_axi_awlen,
    .s_axi_awsize,
    .s_axi_awburst,
    .s_axi_awlock,
    .s_axi_awcache,
    .s_axi_awprot,
    .s_axi_awregion,
    .s_axi_awqos,
    .s_axi_awvalid,
    .s_axi_awready,
    .s_axi_wdata,
    .s_axi_wstrb,
    .s_axi_wlast,
    .s_axi_wvalid,
    .s_axi_wready,
    .s_axi_bid,
    .s_axi_bresp,
    .s_axi_bvalid,
    .s_axi_bready,
    .s_axi_arid,
    .s_axi_araddr,
    .s_axi_arlen,
    .s_axi_arsize,
    .s_axi_arburst,
    .s_axi_arlock,
    .s_axi_arcache,
    .s_axi_arprot,
    .s_axi_arregion,
    .s_axi_arqos,
    .s_axi_arvalid,
    .s_axi_arready,
    .s_axi_rid,
    .s_axi_rdata,
    .s_axi_rresp,
    .s_axi_rlast,
    .s_axi_rvalid,
    .s_axi_rready,
    .m_axi_awaddr,
    .m_axi_awlen,
    .m_axi_awsize,
    .m_axi_awburst,
    .m_axi_awlock,
    .m_axi_awcache,
    .m_axi_awprot,
    .m_axi_awregion,
    .m_axi_awqos,
    .m_axi_awvalid,
    .m_axi_awready,
    .m_axi_wdata,
    .m_axi_wstrb,
    .m_axi_wlast,
    .m_axi_wvalid,
    .m_axi_wready,
    .m_axi_bresp,
    .m_axi_bvalid,
    .m_axi_bready,
    .m_axi_araddr,
    .m_axi_arlen,
    .m_axi_arsize,
    .m_axi_arburst,
    .m_axi_arlock,
    .m_axi_arcache,
    .m_axi_arprot,
    .m_axi_arregion,
    .m_axi_arqos,
    .m_axi_arvalid,
    .m_axi_arready,
    .m_axi_rdata,
    .m_axi_rresp,
    .m_axi_rlast,
    .m_axi_rvalid,
    .m_axi_rready
);

ddr4_0 ddr_i (
    .sys_rst, // input
    .c0_sys_clk_p,
    .c0_sys_clk_n,
    .c0_ddr4_act_n,
    .c0_ddr4_adr,
    .c0_ddr4_ba,
    .c0_ddr4_bg,
    .c0_ddr4_cke,
    .c0_ddr4_odt,
    .c0_ddr4_cs_n,
    .c0_ddr4_ck_t,
    .c0_ddr4_ck_c,
    .c0_ddr4_reset_n,
    .c0_ddr4_dm_dbi_n,
    .c0_ddr4_dq,
    .c0_ddr4_dqs_c,
    .c0_ddr4_dqs_t,
    .c0_init_calib_complete,
    .c0_ddr4_ui_clk, // 1/4 of PHY clock, 300/4 = 75 MHz
    .c0_ddr4_ui_clk_sync_rst,
    .addn_ui_clkout1,
    .dbg_clk(), // output
    .c0_ddr4_aresetn(ndmreset_n),
    .c0_ddr4_s_axi_awid('0),
    .c0_ddr4_s_axi_awaddr(m_axi_awaddr),
    .c0_ddr4_s_axi_awlen(m_axi_awlen),
    .c0_ddr4_s_axi_awsize(m_axi_awsize),
    .c0_ddr4_s_axi_awburst(m_axi_awburst),
    .c0_ddr4_s_axi_awlock(m_axi_awlock),
    .c0_ddr4_s_axi_awcache(m_axi_awcache),
    .c0_ddr4_s_axi_awprot(m_axi_awprot),
    .c0_ddr4_s_axi_awqos(m_axi_awqos),
    .c0_ddr4_s_axi_awvalid(m_axi_awvalid),
    .c0_ddr4_s_axi_awready(m_axi_awready),
    .c0_ddr4_s_axi_wdata(m_axi_wdata),
    .c0_ddr4_s_axi_wstrb(m_axi_wstrb),
    .c0_ddr4_s_axi_wlast(m_axi_wlast),
    .c0_ddr4_s_axi_wvalid(m_axi_wvalid),
    .c0_ddr4_s_axi_wready(m_axi_wready),
    .c0_ddr4_s_axi_bready(m_axi_bready),
    .c0_ddr4_s_axi_bid(),
    .c0_ddr4_s_axi_bresp(m_axi_bresp),
    .c0_ddr4_s_axi_bvalid(m_axi_bvalid),
    .c0_ddr4_s_axi_arid('0),
    .c0_ddr4_s_axi_araddr(m_axi_araddr),
    .c0_ddr4_s_axi_arlen(m_axi_arlen),
    .c0_ddr4_s_axi_arsize(m_axi_arsize),
    .c0_ddr4_s_axi_arburst(m_axi_arburst),
    .c0_ddr4_s_axi_arlock(m_axi_arlock),
    .c0_ddr4_s_axi_arcache(m_axi_arcache),
    .c0_ddr4_s_axi_arprot(m_axi_arprot),
    .c0_ddr4_s_axi_arqos(m_axi_arqos),
    .c0_ddr4_s_axi_arvalid(m_axi_arvalid),
    .c0_ddr4_s_axi_arready(m_axi_arready),
    .c0_ddr4_s_axi_rready(m_axi_rready),
    .c0_ddr4_s_axi_rid(),
    .c0_ddr4_s_axi_rdata(m_axi_rdata),
    .c0_ddr4_s_axi_rresp(m_axi_rresp),
    .c0_ddr4_s_axi_rlast(m_axi_rlast),
    .c0_ddr4_s_axi_rvalid(m_axi_rvalid),
    .dbg_bus()
);

endmodule