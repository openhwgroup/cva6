// Copyright (c) 2020 Thales.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Sebastien Jacq Thales Research & Technology
// Date: 07/12/2017
//
// Additional contributions by:
//         Sebastien Jacq - sjthales on github.com
//
// Description: Zybo z7-20 FPGA platform top module.
//
// =========================================================================== //
// Revisions  :
// Date        Version  Author       Description
// 2020-12-07  0.1      S.Jacq       Top module of Zybo z7-20 FPGA platform
// =========================================================================== //

module cva6_fpga_xilinx (

  input  logic     clk_sys   ,
  input  logic     cpu_reset ,

`ifdef PS7_DDR
  inout wire [14:0]DDR_addr,
  inout wire [2:0]DDR_ba,
  inout wire DDR_cas_n,
  inout wire DDR_ck_n,
  inout wire DDR_ck_p,
  inout wire DDR_cke,
  inout wire DDR_cs_n,
  inout wire [3:0]DDR_dm,
  inout wire [31:0]DDR_dq,
  inout wire [3:0]DDR_dqs_n,
  inout wire [3:0]DDR_dqs_p,
  inout wire DDR_odt,
  inout wire DDR_ras_n,
  inout wire DDR_reset_n,
  inout wire DDR_we_n,
  inout wire ddr_vrn,
  inout wire ddr_vrp,

  inout wire [53:0]mio,
  inout wire ps_clk,
  inout wire ps_porb,
  inout wire ps_srstb,
`endif


  // common part
  input logic      trst_n    ,
  input  logic     tck       ,
  input  logic     tms       ,
  input  logic     tdi       ,
  output wire      tdo       ,
  input  logic     rx        ,
  output logic     tx	




);

// CVA6 config
localparam bit IsRVFI = bit'(0);
// CVA6 Xilinx configuration
function automatic config_pkg::cva6_cfg_t build_fpga_config(config_pkg::cva6_user_cfg_t CVA6UserCfg);
  config_pkg::cva6_user_cfg_t cfg = CVA6UserCfg;
  cfg.RVZiCond = bit'(0);
  cfg.NrNonIdempotentRules = unsigned'(1);
  cfg.NonIdempotentAddrBase = 1024'({64'b0});
  cfg.NonIdempotentLength = 1024'({ariane_soc::DRAMBase});
  return build_config_pkg::build_config(cfg);
endfunction

// CVA6 Xilinx configuration
localparam config_pkg::cva6_cfg_t CVA6Cfg = build_fpga_config(cva6_config_pkg::cva6_cfg);

localparam type rvfi_probes_instr_t = `RVFI_PROBES_INSTR_T(CVA6Cfg);
localparam type rvfi_probes_csr_t = `RVFI_PROBES_CSR_T(CVA6Cfg);
localparam type rvfi_probes_t = struct packed {
  logic csr;
  logic instr;
};

localparam type rvfi_instr_t = logic;


// 24 MByte in 8 byte words
localparam NumWords = (24 * 1024 * 1024) / 8;
// WARNING: If NBSlave is modified, Xilinx's IPs under fpga/xilinx need to be updated with the new AXI id width and regenerated.
// Otherwise reads and writes to DRAM may be returned to the wrong master and the crossbar will freeze. See issue #568.

localparam NBSlave = 2; // debug, ariane
localparam AxiAddrWidth = 64;
localparam AxiDataWidth = 64;
localparam AxiIdWidthMaster = 4;
localparam AxiIdWidthSlaves = AxiIdWidthMaster + $clog2(NBSlave); // 5
localparam AxiUserWidth = CVA6Cfg.AxiUserWidth;

`AXI_TYPEDEF_ALL(axi_slave,
                 logic [    AxiAddrWidth-1:0],
                 logic [AxiIdWidthSlaves-1:0],
                 logic [    AxiDataWidth-1:0],
                 logic [(AxiDataWidth/8)-1:0],
                 logic [    AxiUserWidth-1:0])

AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthMaster ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) slave[NBSlave-1:0]();

AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) master[ariane_soc::NB_PERIPHERALS-1:0]();

AXI_BUS #(
    .AXI_ADDR_WIDTH ( CVA6Cfg.XLEN      ),
    .AXI_DATA_WIDTH ( CVA6Cfg.XLEN      ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) master_to_dm[0:0]();

// disable test-enable
logic test_en;
logic ndmreset;
logic ndmreset_n;
logic debug_req_irq;
logic timer_irq;
logic ipi;

logic clk;
logic eth_clk;
logic spi_clk_i;
logic phy_tx_clk;
logic sd_clk_sys;


logic ps_clock_out;

logic rst_n, rst;
logic rtc;


//assign trst_n = 1'b1;
//assign trst_n = ndmreset_n;

logic pll_locked;

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

// IRQ
logic [1:0] irq;
assign test_en    = 1'b0;

logic [NBSlave-1:0] pc_asserted;

logic dmi_trst_n;

rstgen i_rstgen_main (
    .clk_i        ( clk                      ),
    .rst_ni       ( pll_locked & (~ndmreset) ),
    .test_mode_i  ( test_en                  ),
    .rst_no       ( ndmreset_n               ),
    .init_no      (                          ) // keep open
);


assign rst_n = ~cpu_reset;
assign rst = cpu_reset;

// ---------------
// AXI Xbar
// ---------------

axi_pkg::xbar_rule_64_t [ariane_soc::NB_PERIPHERALS-1:0] addr_map;

assign addr_map = '{
  '{ idx: ariane_soc::Debug,    start_addr: ariane_soc::DebugBase,    end_addr: ariane_soc::DebugBase + ariane_soc::DebugLength       },
  '{ idx: ariane_soc::ROM,      start_addr: ariane_soc::ROMBase,      end_addr: ariane_soc::ROMBase + ariane_soc::ROMLength           },
  '{ idx: ariane_soc::CLINT,    start_addr: ariane_soc::CLINTBase,    end_addr: ariane_soc::CLINTBase + ariane_soc::CLINTLength       },
  '{ idx: ariane_soc::PLIC,     start_addr: ariane_soc::PLICBase,     end_addr: ariane_soc::PLICBase + ariane_soc::PLICLength         },
  '{ idx: ariane_soc::UART,     start_addr: ariane_soc::UARTBase,     end_addr: ariane_soc::UARTBase + ariane_soc::UARTLength         },
  '{ idx: ariane_soc::Timer,    start_addr: ariane_soc::TimerBase,    end_addr: ariane_soc::TimerBase + ariane_soc::TimerLength       },
  '{ idx: ariane_soc::SPI,      start_addr: ariane_soc::SPIBase,      end_addr: ariane_soc::SPIBase + ariane_soc::SPILength           },
  '{ idx: ariane_soc::Ethernet, start_addr: ariane_soc::EthernetBase, end_addr: ariane_soc::EthernetBase + ariane_soc::EthernetLength },
  '{ idx: ariane_soc::GPIO,     start_addr: ariane_soc::GPIOBase,     end_addr: ariane_soc::GPIOBase + ariane_soc::GPIOLength         },
  '{ idx: ariane_soc::DRAM,     start_addr: ariane_soc::DRAMBase,     end_addr: ariane_soc::DRAMBase + ariane_soc::DRAMLength         }
};

localparam axi_pkg::xbar_cfg_t AXI_XBAR_CFG = '{
  NoSlvPorts:         ariane_soc::NrSlaves,
  NoMstPorts:         ariane_soc::NB_PERIPHERALS,
  MaxMstTrans:        1, // Probably requires update
  MaxSlvTrans:        1, // Probably requires update
  FallThrough:        1'b0,
  LatencyMode:        axi_pkg::CUT_ALL_PORTS,
  AxiIdWidthSlvPorts: AxiIdWidthMaster,
  AxiIdUsedSlvPorts:  AxiIdWidthMaster,
  UniqueIds:          1'b0,
  AxiAddrWidth:       AxiAddrWidth,
  AxiDataWidth:       AxiDataWidth,
  NoAddrRules:        ariane_soc::NB_PERIPHERALS
};

axi_xbar_intf #(
  .AXI_USER_WIDTH ( AxiUserWidth            ),
  .Cfg            ( AXI_XBAR_CFG            ),
  .rule_t         ( axi_pkg::xbar_rule_64_t )
) i_axi_xbar (
  .clk_i                 ( clk        ),
  .rst_ni                ( ndmreset_n ),
  .test_i                ( test_en    ),
  .slv_ports             ( slave      ),
  .mst_ports             ( master     ),
  .addr_map_i            ( addr_map   ),
  .en_default_mst_port_i ( '0         ),
  .default_mst_port_i    ( '0         )
);


//`ifdef LAUTERBACH_DEBUG_PROBE
  assign dmi_trst_n = trst_n;
//`else
//  assign dmi_trst_n = 1'b1;
//`endif

// ---------------
// Debug Module
// ---------------
dmi_jtag  #(
        .IdcodeValue          ( 32'h249511C3    )
    )i_dmi_jtag (
    .clk_i                ( clk                  ),
    .rst_ni               ( rst_n                ),
    .dmi_rst_no           (                      ), // keep open
    .testmode_i           ( test_en              ),
    .dmi_req_valid_o      ( debug_req_valid      ),
    .dmi_req_ready_i      ( debug_req_ready      ),
    .dmi_req_o            ( debug_req            ),
    .dmi_resp_valid_i     ( debug_resp_valid     ),
    .dmi_resp_ready_o     ( debug_resp_ready     ),
    .dmi_resp_i           ( debug_resp           ),
    .tck_i                ( tck    ),
    .tms_i                ( tms    ),
    .trst_ni              ( dmi_trst_n ),
    .td_i                 ( tdi    ),
    .td_o                 ( tdo    ),
    .tdo_oe_o             (        )
);

ariane_axi::req_t    dm_axi_m_req;
ariane_axi::resp_t   dm_axi_m_resp;


logic                      dm_slave_req;
logic                      dm_slave_we;
logic [CVA6Cfg.XLEN-1:0]    dm_slave_addr;
logic [CVA6Cfg.XLEN/8-1:0]  dm_slave_be;
logic [CVA6Cfg.XLEN-1:0]    dm_slave_wdata;
logic [CVA6Cfg.XLEN-1:0]    dm_slave_rdata;

logic                      dm_master_req;
logic [CVA6Cfg.XLEN-1:0]    dm_master_add;
logic                      dm_master_we;
logic [CVA6Cfg.XLEN-1:0]    dm_master_wdata;
logic [CVA6Cfg.XLEN/8-1:0]  dm_master_be;
logic                      dm_master_gnt;
logic                      dm_master_r_valid;
logic [CVA6Cfg.XLEN-1:0]    dm_master_r_rdata;

// debug module
dm_top #(
    .NrHarts          ( 1                 ),
    .BusWidth         ( CVA6Cfg.XLEN      ),
    .SelectableHarts  ( 1'b1              )
) i_dm_top (
    .clk_i            ( clk               ),
    .rst_ni           ( rst_n             ), // PoR
    .testmode_i       ( test_en           ),
    .ndmreset_o       ( ndmreset          ),
    .dmactive_o       ( dmactive          ), // active debug session
    .debug_req_o      ( debug_req_irq     ),
    .unavailable_i    ( '0                ),
    .hartinfo_i       ( {ariane_pkg::DebugHartInfo} ),
    .slave_req_i      ( dm_slave_req      ),
    .slave_we_i       ( dm_slave_we       ),
    .slave_addr_i     ( dm_slave_addr     ),
    .slave_be_i       ( dm_slave_be       ),
    .slave_wdata_i    ( dm_slave_wdata    ),
    .slave_rdata_o    ( dm_slave_rdata    ),
    .master_req_o     ( dm_master_req     ),
    .master_add_o     ( dm_master_add     ),
    .master_we_o      ( dm_master_we      ),
    .master_wdata_o   ( dm_master_wdata   ),
    .master_be_o      ( dm_master_be      ),
    .master_gnt_i     ( dm_master_gnt     ),
    .master_r_valid_i ( dm_master_r_valid ),
    .master_r_rdata_i ( dm_master_r_rdata ),
    .dmi_rst_ni       ( rst_n             ),
    .dmi_req_valid_i  ( debug_req_valid   ),
    .dmi_req_ready_o  ( debug_req_ready   ),
    .dmi_req_i        ( debug_req         ),
    .dmi_resp_valid_o ( debug_resp_valid  ),
    .dmi_resp_ready_i ( debug_resp_ready  ),
    .dmi_resp_o       ( debug_resp        )
);

axi2mem #(
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves    ),
    .AXI_ADDR_WIDTH ( CVA6Cfg.XLEN        ),
    .AXI_DATA_WIDTH ( CVA6Cfg.XLEN        ),
    .AXI_USER_WIDTH ( AxiUserWidth        )
) i_dm_axi2mem (
    .clk_i      ( clk                       ),
    .rst_ni     ( rst_n                     ),
    .slave      ( master_to_dm[0]           ),
    .req_o      ( dm_slave_req              ),
    .we_o       ( dm_slave_we               ),
    .addr_o     ( dm_slave_addr             ),
    .be_o       ( dm_slave_be               ),
    .data_o     ( dm_slave_wdata            ),
    .data_i     ( dm_slave_rdata            )
);

if (CVA6Cfg.XLEN==32 ) begin

    assign master_to_dm[0].aw_user = '0;
    assign master_to_dm[0].w_user = '0;
    assign master_to_dm[0].ar_user = '0;

    assign master_to_dm[0].aw_id = dm_axi_m_req.aw.id;
    assign master_to_dm[0].ar_id = dm_axi_m_req.ar.id;

    assign master[ariane_soc::Debug].r_user ='0;
    assign master[ariane_soc::Debug].b_user ='0;

    xlnx_axi_dwidth_converter_dm_slave  i_axi_dwidth_converter_dm_slave(
        .s_axi_aclk(clk),
        .s_axi_aresetn(ndmreset_n),
        .s_axi_awid(master[ariane_soc::Debug].aw_id),
        .s_axi_awaddr(master[ariane_soc::Debug].aw_addr[31:0]),
        .s_axi_awlen(master[ariane_soc::Debug].aw_len),
        .s_axi_awsize(master[ariane_soc::Debug].aw_size),
        .s_axi_awburst(master[ariane_soc::Debug].aw_burst),
        .s_axi_awlock(master[ariane_soc::Debug].aw_lock),
        .s_axi_awcache(master[ariane_soc::Debug].aw_cache),
        .s_axi_awprot(master[ariane_soc::Debug].aw_prot),
        .s_axi_awregion(master[ariane_soc::Debug].aw_region),
        .s_axi_awqos(master[ariane_soc::Debug].aw_qos),
        .s_axi_awvalid(master[ariane_soc::Debug].aw_valid),
        .s_axi_awready(master[ariane_soc::Debug].aw_ready),
        .s_axi_wdata(master[ariane_soc::Debug].w_data),
        .s_axi_wstrb(master[ariane_soc::Debug].w_strb),
        .s_axi_wlast(master[ariane_soc::Debug].w_last),
        .s_axi_wvalid(master[ariane_soc::Debug].w_valid),
        .s_axi_wready(master[ariane_soc::Debug].w_ready),
        .s_axi_bid(master[ariane_soc::Debug].b_id),
        .s_axi_bresp(master[ariane_soc::Debug].b_resp),
        .s_axi_bvalid(master[ariane_soc::Debug].b_valid),
        .s_axi_bready(master[ariane_soc::Debug].b_ready),
        .s_axi_arid(master[ariane_soc::Debug].ar_id),
        .s_axi_araddr(master[ariane_soc::Debug].ar_addr[31:0]),
        .s_axi_arlen(master[ariane_soc::Debug].ar_len),
        .s_axi_arsize(master[ariane_soc::Debug].ar_size),
        .s_axi_arburst(master[ariane_soc::Debug].ar_burst),
        .s_axi_arlock(master[ariane_soc::Debug].ar_lock),
        .s_axi_arcache(master[ariane_soc::Debug].ar_cache),
        .s_axi_arprot(master[ariane_soc::Debug].ar_prot),
        .s_axi_arregion(master[ariane_soc::Debug].ar_region),
        .s_axi_arqos(master[ariane_soc::Debug].ar_qos),
        .s_axi_arvalid(master[ariane_soc::Debug].ar_valid),
        .s_axi_arready(master[ariane_soc::Debug].ar_ready),
        .s_axi_rid(master[ariane_soc::Debug].r_id),
        .s_axi_rdata(master[ariane_soc::Debug].r_data),
        .s_axi_rresp(master[ariane_soc::Debug].r_resp),
        .s_axi_rlast(master[ariane_soc::Debug].r_last),
        .s_axi_rvalid(master[ariane_soc::Debug].r_valid),
        .s_axi_rready(master[ariane_soc::Debug].r_ready),
        .m_axi_awaddr(master_to_dm[0].aw_addr),
        .m_axi_awlen(master_to_dm[0].aw_len),
        .m_axi_awsize(master_to_dm[0].aw_size),
        .m_axi_awburst(master_to_dm[0].aw_burst),
        .m_axi_awlock(master_to_dm[0].aw_lock),
        .m_axi_awcache(master_to_dm[0].aw_cache),
        .m_axi_awprot(master_to_dm[0].aw_prot),
        .m_axi_awregion(master_to_dm[0].aw_region),
        .m_axi_awqos(master_to_dm[0].aw_qos),
        .m_axi_awvalid(master_to_dm[0].aw_valid),
        .m_axi_awready(master_to_dm[0].aw_ready),
        .m_axi_wdata(master_to_dm[0].w_data ),
        .m_axi_wstrb(master_to_dm[0].w_strb),
        .m_axi_wlast(master_to_dm[0].w_last),
        .m_axi_wvalid(master_to_dm[0].w_valid),
        .m_axi_wready(master_to_dm[0].w_ready),
        .m_axi_bresp(master_to_dm[0].b_resp),
        .m_axi_bvalid(master_to_dm[0].b_valid),
        .m_axi_bready(master_to_dm[0].b_ready),
        .m_axi_araddr(master_to_dm[0].ar_addr),
        .m_axi_arlen(master_to_dm[0].ar_len),
        .m_axi_arsize(master_to_dm[0].ar_size),
        .m_axi_arburst(master_to_dm[0].ar_burst),
        .m_axi_arlock(master_to_dm[0].ar_lock),
        .m_axi_arcache(master_to_dm[0].ar_cache),
        .m_axi_arprot(master_to_dm[0].ar_prot),
        .m_axi_arregion(master_to_dm[0].ar_region),
        .m_axi_arqos(master_to_dm[0].ar_qos),
        .m_axi_arvalid(master_to_dm[0].ar_valid),
        .m_axi_arready(master_to_dm[0].ar_ready),
        .m_axi_rdata(master_to_dm[0].r_data),
        .m_axi_rresp(master_to_dm[0].r_resp),
        .m_axi_rlast(master_to_dm[0].r_last),
        .m_axi_rvalid(master_to_dm[0].r_valid),
        .m_axi_rready(master_to_dm[0].r_ready)
    );

end else begin

    assign master[ariane_soc::Debug].aw_id = master_to_dm[0].aw_id;
    assign master[ariane_soc::Debug].aw_addr = master_to_dm[0].aw_addr;
    assign master[ariane_soc::Debug].aw_len = master_to_dm[0].aw_len;
    assign master[ariane_soc::Debug].aw_size = master_to_dm[0].aw_size;
    assign master[ariane_soc::Debug].aw_burst = master_to_dm[0].aw_burst;
    assign master[ariane_soc::Debug].aw_lock = master_to_dm[0].aw_lock;
    assign master[ariane_soc::Debug].aw_cache = master_to_dm[0].aw_cache;
    assign master[ariane_soc::Debug].aw_prot = master_to_dm[0].aw_prot;
    assign master[ariane_soc::Debug].aw_qos = master_to_dm[0].aw_qos;
    assign master[ariane_soc::Debug].aw_atop = master_to_dm[0].aw_atop;
    assign master[ariane_soc::Debug].aw_region = master_to_dm[0].aw_region;
    assign master[ariane_soc::Debug].aw_user = master_to_dm[0].aw_user;
    assign master[ariane_soc::Debug].aw_valid = master_to_dm[0].aw_valid;

    assign master_to_dm[0].aw_ready =master[ariane_soc::Debug].aw_ready;

    assign master[ariane_soc::Debug].w_data = master_to_dm[0].w_data;
    assign master[ariane_soc::Debug].w_strb = master_to_dm[0].w_strb;
    assign master[ariane_soc::Debug].w_last = master_to_dm[0].w_last;
    assign master[ariane_soc::Debug].w_user = master_to_dm[0].w_user;
    assign master[ariane_soc::Debug].w_valid = master_to_dm[0].w_valid;

    assign master_to_dm[0].w_ready =master[ariane_soc::Debug].w_ready;

    assign master_to_dm[0].b_id =master[ariane_soc::Debug].b_id;
    assign master_to_dm[0].b_resp =master[ariane_soc::Debug].b_resp;
    assign master_to_dm[0].b_user =master[ariane_soc::Debug].b_user;
    assign master_to_dm[0].b_valid =master[ariane_soc::Debug].b_valid;

    assign master[ariane_soc::Debug].b_ready = master_to_dm[0].b_ready;

    assign master[ariane_soc::Debug].ar_id = master_to_dm[0].ar_id;
    assign master[ariane_soc::Debug].ar_addr = master_to_dm[0].ar_addr;
    assign master[ariane_soc::Debug].ar_len = master_to_dm[0].ar_len;
    assign master[ariane_soc::Debug].ar_size = master_to_dm[0].ar_size;
    assign master[ariane_soc::Debug].ar_burst = master_to_dm[0].ar_burst;
    assign master[ariane_soc::Debug].ar_lock = master_to_dm[0].ar_lock;
    assign master[ariane_soc::Debug].ar_cache = master_to_dm[0].ar_cache;
    assign master[ariane_soc::Debug].ar_prot = master_to_dm[0].ar_prot;
    assign master[ariane_soc::Debug].ar_qos = master_to_dm[0].ar_qos;
    assign master[ariane_soc::Debug].ar_region = master_to_dm[0].ar_region;
    assign master[ariane_soc::Debug].ar_user = master_to_dm[0].ar_user;
    assign master[ariane_soc::Debug].ar_valid = master_to_dm[0].ar_valid;

    assign master_to_dm[0].ar_ready =master[ariane_soc::Debug].ar_ready;

    assign master_to_dm[0].r_id =master[ariane_soc::Debug].r_id;
    assign master_to_dm[0].r_data =master[ariane_soc::Debug].r_data;
    assign master_to_dm[0].r_resp =master[ariane_soc::Debug].r_resp;
    assign master_to_dm[0].r_last =master[ariane_soc::Debug].r_last;
    assign master_to_dm[0].r_user =master[ariane_soc::Debug].r_user;
    assign master_to_dm[0].r_valid =master[ariane_soc::Debug].r_valid;

    assign master[ariane_soc::Debug].r_ready = master_to_dm[0].r_ready;

end



logic [1:0]    axi_adapter_size;

assign axi_adapter_size = (CVA6Cfg.XLEN == 64) ? 2'b11 : 2'b10;

axi_adapter #(
    .CVA6Cfg               ( CVA6Cfg                  ),
    .DATA_WIDTH            ( CVA6Cfg.XLEN              ),
    .axi_req_t             ( ariane_axi::req_t        ),
    .axi_rsp_t             ( ariane_axi::resp_t       )
) i_dm_axi_master (
    .clk_i                 ( clk                       ),
    .rst_ni                ( rst_n                     ),
    .req_i                 ( dm_master_req             ),
    .type_i                ( ariane_pkg::SINGLE_REQ    ),
    .amo_i                 ( ariane_pkg::AMO_NONE      ),
    .gnt_o                 ( dm_master_gnt             ),
    .addr_i                ( dm_master_add             ),
    .we_i                  ( dm_master_we              ),
    .wdata_i               ( dm_master_wdata           ),
    .be_i                  ( dm_master_be              ),
    .size_i                ( axi_adapter_size          ),
    .id_i                  ( '0                        ),
    .valid_o               ( dm_master_r_valid         ),
    .rdata_o               ( dm_master_r_rdata         ),
    .id_o                  (                           ),
    .critical_word_o       (                           ),
    .critical_word_valid_o (                           ),
    .axi_req_o             ( dm_axi_m_req              ),
    .axi_resp_i            ( dm_axi_m_resp             )
);

if (CVA6Cfg.XLEN==32 ) begin
    logic [31 : 0] dm_master_m_awaddr;
    logic [31 : 0] dm_master_m_araddr;

    assign slave[1].aw_addr = {32'h0000_0000, dm_master_m_awaddr};
    assign slave[1].ar_addr = {32'h0000_0000, dm_master_m_araddr};

    logic [31 : 0] dm_master_s_rdata;

    assign dm_axi_m_resp.r.data = {32'h0000_0000, dm_master_s_rdata};

    assign slave[1].aw_user = '0;
    assign slave[1].w_user = '0;
    assign slave[1].ar_user = '0;

    assign slave[1].aw_id = dm_axi_m_req.aw.id;
    assign slave[1].ar_id = dm_axi_m_req.ar.id;
    assign slave[1].aw_atop = dm_axi_m_req.aw.atop;

    xlnx_axi_dwidth_converter_dm_master  i_axi_dwidth_converter_dm_master(
        .s_axi_aclk(clk),
        .s_axi_aresetn(ndmreset_n),
        .s_axi_awid(dm_axi_m_req.aw.id),
        .s_axi_awaddr(dm_axi_m_req.aw.addr[31:0]),
        .s_axi_awlen(dm_axi_m_req.aw.len),
        .s_axi_awsize(dm_axi_m_req.aw.size),
        .s_axi_awburst(dm_axi_m_req.aw.burst),
        .s_axi_awlock(dm_axi_m_req.aw.lock),
        .s_axi_awcache(dm_axi_m_req.aw.cache),
        .s_axi_awprot(dm_axi_m_req.aw.prot),
        .s_axi_awregion(dm_axi_m_req.aw.region),
        .s_axi_awqos(dm_axi_m_req.aw.qos),
        .s_axi_awvalid(dm_axi_m_req.aw_valid),
        .s_axi_awready(dm_axi_m_resp.aw_ready),
        .s_axi_wdata(dm_axi_m_req.w.data[31:0]),
        .s_axi_wstrb(dm_axi_m_req.w.strb[3:0]),
        .s_axi_wlast(dm_axi_m_req.w.last),
        .s_axi_wvalid(dm_axi_m_req.w_valid),
        .s_axi_wready(dm_axi_m_resp.w_ready),
        .s_axi_bid(dm_axi_m_resp.b.id),
        .s_axi_bresp(dm_axi_m_resp.b.resp),
        .s_axi_bvalid(dm_axi_m_resp.b_valid),
        .s_axi_bready(dm_axi_m_req.b_ready),
        .s_axi_arid(dm_axi_m_req.ar.id),
        .s_axi_araddr(dm_axi_m_req.ar.addr[31:0]),
        .s_axi_arlen(dm_axi_m_req.ar.len),
        .s_axi_arsize(dm_axi_m_req.ar.size),
        .s_axi_arburst(dm_axi_m_req.ar.burst),
        .s_axi_arlock(dm_axi_m_req.ar.lock),
        .s_axi_arcache(dm_axi_m_req.ar.cache),
        .s_axi_arprot(dm_axi_m_req.ar.prot),
        .s_axi_arregion(dm_axi_m_req.ar.region),
        .s_axi_arqos(dm_axi_m_req.ar.qos),
        .s_axi_arvalid(dm_axi_m_req.ar_valid),
        .s_axi_arready(dm_axi_m_resp.ar_ready),
        .s_axi_rid(dm_axi_m_resp.r.id),
        .s_axi_rdata(dm_master_s_rdata),
        .s_axi_rresp(dm_axi_m_resp.r.resp),
        .s_axi_rlast(dm_axi_m_resp.r.last),
        .s_axi_rvalid(dm_axi_m_resp.r_valid),
        .s_axi_rready(dm_axi_m_req.r_ready),
        .m_axi_awaddr(dm_master_m_awaddr),
        .m_axi_awlen(slave[1].aw_len),
        .m_axi_awsize(slave[1].aw_size),
        .m_axi_awburst(slave[1].aw_burst),
        .m_axi_awlock(slave[1].aw_lock),
        .m_axi_awcache(slave[1].aw_cache),
        .m_axi_awprot(slave[1].aw_prot),
        .m_axi_awregion(slave[1].aw_region),
        .m_axi_awqos(slave[1].aw_qos),
        .m_axi_awvalid(slave[1].aw_valid),
        .m_axi_awready(slave[1].aw_ready),
        .m_axi_wdata(slave[1].w_data ),
        .m_axi_wstrb(slave[1].w_strb),
        .m_axi_wlast(slave[1].w_last),
        .m_axi_wvalid(slave[1].w_valid),
        .m_axi_wready(slave[1].w_ready),
        .m_axi_bresp(slave[1].b_resp),
        .m_axi_bvalid(slave[1].b_valid),
        .m_axi_bready(slave[1].b_ready),
        .m_axi_araddr(dm_master_m_araddr),
        .m_axi_arlen(slave[1].ar_len),
        .m_axi_arsize(slave[1].ar_size),
        .m_axi_arburst(slave[1].ar_burst),
        .m_axi_arlock(slave[1].ar_lock),
        .m_axi_arcache(slave[1].ar_cache),
        .m_axi_arprot(slave[1].ar_prot),
        .m_axi_arregion(slave[1].ar_region),
        .m_axi_arqos(slave[1].ar_qos),
        .m_axi_arvalid(slave[1].ar_valid),
        .m_axi_arready(slave[1].ar_ready),
        .m_axi_rdata(slave[1].r_data),
        .m_axi_rresp(slave[1].r_resp),
        .m_axi_rlast(slave[1].r_last),
        .m_axi_rvalid(slave[1].r_valid),
        .m_axi_rready(slave[1].r_ready)
      );
end else begin
    `AXI_ASSIGN_FROM_REQ(slave[1], dm_axi_m_req)
    `AXI_ASSIGN_TO_RESP(dm_axi_m_resp, slave[1])
end


// ---------------
// Core
// ---------------
ariane_axi::req_t    axi_ariane_req;
ariane_axi::resp_t   axi_ariane_resp;

ariane #(
    .CVA6Cfg ( CVA6Cfg ),
    .rvfi_probes_instr_t ( rvfi_probes_instr_t ),
    .rvfi_probes_csr_t ( rvfi_probes_csr_t ),
    .rvfi_probes_t ( rvfi_probes_t )
) i_ariane (
    .clk_i        ( clk                 ),
    .rst_ni       ( ndmreset_n          ),
    .boot_addr_i  ( ariane_soc::ROMBase ), // start fetching from ROM
    .hart_id_i    ( '0                  ),
    .irq_i        ( irq                 ),
    .ipi_i        ( ipi                 ),
    .time_irq_i   ( timer_irq           ),
    .rvfi_probes_o( /* open */          ),
    .debug_req_i  ( debug_req_irq       ),
    .noc_req_o    ( axi_ariane_req      ),
    .noc_resp_i   ( axi_ariane_resp     )
);

`AXI_ASSIGN_FROM_REQ(slave[0], axi_ariane_req)
`AXI_ASSIGN_TO_RESP(axi_ariane_resp, slave[0])

// ---------------
// CLINT
// ---------------
// divide clock by two
always_ff @(posedge clk or negedge ndmreset_n) begin
  if (~ndmreset_n) begin
    rtc <= 0;
  end else begin
    rtc <= rtc ^ 1'b1;
  end
end

axi_slave_req_t  axi_clint_req;
axi_slave_resp_t axi_clint_resp;

clint #(
    .CVA6Cfg        ( CVA6Cfg          ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .NR_CORES       ( 1                ),
    .axi_req_t      ( axi_slave_req_t  ),
    .axi_resp_t     ( axi_slave_resp_t )
) i_clint (
    .clk_i       ( clk            ),
    .rst_ni      ( ndmreset_n     ),
    .testmode_i  ( test_en        ),
    .axi_req_i   ( axi_clint_req  ),
    .axi_resp_o  ( axi_clint_resp ),
    .rtc_i       ( rtc            ),
    .timer_irq_o ( timer_irq      ),
    .ipi_o       ( ipi            )
);

`AXI_ASSIGN_TO_REQ(axi_clint_req, master[ariane_soc::CLINT])
`AXI_ASSIGN_FROM_RESP(master[ariane_soc::CLINT], axi_clint_resp)

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

if (CVA6Cfg.XLEN==32 ) begin
    bootrom_32 i_bootrom (
        .clk_i   ( clk       ),
        .req_i   ( rom_req   ),
        .addr_i  ( rom_addr  ),
        .rdata_o ( rom_rdata )
    );
end else begin
    bootrom_64 i_bootrom (
        .clk_i   ( clk       ),
        .req_i   ( rom_req   ),
        .addr_i  ( rom_addr  ),
        .rdata_o ( rom_rdata )
    );
end

// ---------------
// Peripherals
// ---------------

ariane_peripherals #(
    .AxiAddrWidth ( AxiAddrWidth     ),
    .AxiDataWidth ( AxiDataWidth     ),
    .AxiIdWidth   ( AxiIdWidthSlaves ),
    .AxiUserWidth ( AxiUserWidth     ),
    .InclUART     ( 1'b1             ),
    .InclGPIO     ( 1'b0             ),
    .InclSPI      ( 1'b0         ),
    .InclEthernet ( 1'b0         )

) i_ariane_peripherals (
    .clk_i        ( clk                          ),
    .clk_200MHz_i ( 1'b0               ),
    .rst_ni       ( ndmreset_n                   ),
    .plic         ( master[ariane_soc::PLIC]     ),
    .uart         ( master[ariane_soc::UART]     ),
    .spi          ( master[ariane_soc::SPI]      ),
    .gpio         ( master[ariane_soc::GPIO]     ),
    .eth_clk_i    ( eth_clk                      ),
    .ethernet     ( master[ariane_soc::Ethernet] ),
    .timer        ( master[ariane_soc::Timer]    ),
    .irq_o        ( irq                          ),
    .rx_i         ( rx                           ),
    .tx_o         ( tx                           ),
    .eth_txck (),
    .eth_rxck (1'b0),
    .eth_rxctl (1'b0),
    .eth_rxd (4'b0000),
    .eth_rst_n (),
    .eth_txctl (),
    .eth_txd (),
    .eth_mdio (),
    .eth_mdc (),
    .phy_tx_clk_i   ( phy_tx_clk                  ),
    .sd_clk_i       ( sd_clk_sys                  ),
    .spi_clk_o      ( spi_clk_o                   ),
    .spi_mosi       ( spi_mosi                    ),
    .spi_miso       ( spi_miso                    ),
    .spi_ss         ( spi_ss                      ),

      .leds_o         (                        ),
      .dip_switches_i (                        )

);


// ---------------------
// Board peripherals
// ---------------------
// ---------------
// DDR
// ---------------
logic [AxiIdWidthSlaves-1:0] s_axi_awid;
logic [AxiAddrWidth-1:0]     s_axi_awaddr;
logic [7:0]                  s_axi_awlen;
logic [2:0]                  s_axi_awsize;
logic [1:0]                  s_axi_awburst;
logic [0:0]                  s_axi_awlock;
logic [3:0]                  s_axi_awcache;
logic [2:0]                  s_axi_awprot;
logic [3:0]                  s_axi_awregion;
logic [3:0]                  s_axi_awqos;
logic                        s_axi_awvalid;
logic                        s_axi_awready;
logic [AxiDataWidth-1:0]     s_axi_wdata;
logic [AxiDataWidth/8-1:0]   s_axi_wstrb;
logic                        s_axi_wlast;
logic                        s_axi_wvalid;
logic                        s_axi_wready;
logic [AxiIdWidthSlaves-1:0] s_axi_bid;
logic [1:0]                  s_axi_bresp;
logic                        s_axi_bvalid;
logic                        s_axi_bready;
logic [AxiIdWidthSlaves-1:0] s_axi_arid;
logic [AxiAddrWidth-1:0]     s_axi_araddr;
logic [7:0]                  s_axi_arlen;
logic [2:0]                  s_axi_arsize;
logic [1:0]                  s_axi_arburst;
logic [0:0]                  s_axi_arlock;
logic [3:0]                  s_axi_arcache;
logic [2:0]                  s_axi_arprot;
logic [3:0]                  s_axi_arregion;
logic [3:0]                  s_axi_arqos;
logic                        s_axi_arvalid;
logic                        s_axi_arready;
logic [AxiIdWidthSlaves-1:0] s_axi_rid;
logic [AxiDataWidth-1:0]     s_axi_rdata;
logic [1:0]                  s_axi_rresp;
logic                        s_axi_rlast;
logic                        s_axi_rvalid;
logic                        s_axi_rready;

AXI_BUS #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( AxiUserWidth     )
) dram();

axi_riscv_atomics_wrap #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth     ),
    .AXI_DATA_WIDTH ( AxiDataWidth     ),
    .AXI_ID_WIDTH   ( AxiIdWidthSlaves ),
    .AXI_USER_WIDTH ( AxiUserWidth     ),
    .AXI_MAX_WRITE_TXNS ( 1  ),
    .RISCV_WORD_WIDTH   ( 64 )
) i_axi_riscv_atomics (
    .clk_i  ( clk                      ),
    .rst_ni ( ndmreset_n               ),
    .slv    ( master[ariane_soc::DRAM] ),
    .mst    ( dram                     )
);


assign dram.r_user = '0;
assign dram.b_user = '0;

xlnx_clk_gen i_xlnx_clk_gen (
  .clk_out1 ( clk           ), // 50 MHz
  .clk_out2 ( phy_tx_clk    ), // 125 MHz (for RGMII PHY)
  .clk_out3 ( eth_clk       ), // 125 MHz quadrature (90 deg phase shift)
  .clk_out4 ( sd_clk_sys    ), // 50 MHz clock
  .reset    ( cpu_reset     ),
  .locked   ( pll_locked    ),
  .clk_in1  ( clk_sys )  //125 MHz
);


logic [31 : 0] saxibram_awaddr;
logic [31 : 0] saxibram_araddr;


assign saxibram_awaddr = dram.aw_addr & 32'h7fff_ffff;
assign saxibram_araddr = dram.ar_addr & 32'h7fff_ffff;


`ifdef PS7_DDR

logic [5:0] S_AXI_HP0_BID;
logic [5:0] S_AXI_HP0_RID;

assign dram.b_id = S_AXI_HP0_BID[4:0];
assign dram.r_id = S_AXI_HP0_RID[4:0];

xlnx_processing_system7 i_xlnx_processing_system7(
 //INTERNAL SIGNALS
    .S_AXI_HP0_ARREADY (dram.ar_ready),//S_AXI_HP0_ARREADY : out STD_LOGIC;
    .S_AXI_HP0_AWREADY (dram.aw_ready),//S_AXI_HP0_AWREADY : out STD_LOGIC;
    .S_AXI_HP0_BVALID (dram.b_valid),//S_AXI_HP0_BVALID : out STD_LOGIC;
    .S_AXI_HP0_RLAST (dram.r_last),//S_AXI_HP0_RLAST : out STD_LOGIC;
    .S_AXI_HP0_RVALID (dram.r_valid),//S_AXI_HP0_RVALID : out STD_LOGIC;
    .S_AXI_HP0_WREADY (dram.w_ready),//S_AXI_HP0_WREADY : out STD_LOGIC;
    .S_AXI_HP0_BRESP (dram.b_resp),//S_AXI_HP0_BRESP : out STD_LOGIC_VECTOR ( 1 downto 0 );
    .S_AXI_HP0_RRESP (dram.r_resp),//S_AXI_HP0_RRESP : out STD_LOGIC_VECTOR ( 1 downto 0 );
    .S_AXI_HP0_BID (S_AXI_HP0_BID),//S_AXI_HP0_BID : out STD_LOGIC_VECTOR ( 5 downto 0 );
    .S_AXI_HP0_RID (S_AXI_HP0_RID),//S_AXI_HP0_RID : out STD_LOGIC_VECTOR ( 5 downto 0 );
    .S_AXI_HP0_RDATA (dram.r_data),//S_AXI_HP0_RDATA : out STD_LOGIC_VECTOR ( 63 downto 0 );
    .S_AXI_HP0_RCOUNT (),//S_AXI_HP0_RCOUNT : out STD_LOGIC_VECTOR ( 7 downto 0 );
    .S_AXI_HP0_WCOUNT (),//S_AXI_HP0_WCOUNT : out STD_LOGIC_VECTOR ( 7 downto 0 );
    .S_AXI_HP0_RACOUNT (),//S_AXI_HP0_RACOUNT : out STD_LOGIC_VECTOR ( 2 downto 0 );
    .S_AXI_HP0_WACOUNT (),//S_AXI_HP0_WACOUNT : out STD_LOGIC_VECTOR ( 5 downto 0 );
    .S_AXI_HP0_ACLK (clk),//S_AXI_HP0_ACLK : in STD_LOGIC;
    .S_AXI_HP0_ARVALID (dram.ar_valid),//S_AXI_HP0_ARVALID : in STD_LOGIC;
    .S_AXI_HP0_AWVALID (dram.aw_valid),//S_AXI_HP0_AWVALID : in STD_LOGIC;
    .S_AXI_HP0_BREADY (dram.b_ready),//S_AXI_HP0_BREADY : in STD_LOGIC;
    .S_AXI_HP0_RDISSUECAP1_EN (1'b0),//S_AXI_HP0_RDISSUECAP1_EN : in STD_LOGIC;
    .S_AXI_HP0_RREADY (dram.r_ready),//S_AXI_HP0_RREADY S_AXI_HP0_RREADY : in STD_LOGIC;
    .S_AXI_HP0_WLAST (dram.w_last),//S_AXI_HP0_WLAST : in STD_LOGIC;
    .S_AXI_HP0_WRISSUECAP1_EN (1'b0),//S_AXI_HP0_WRISSUECAP1_EN : in STD_LOGIC;
    .S_AXI_HP0_WVALID (dram.w_valid),//S_AXI_HP0_WVALID : in STD_LOGIC;
    .S_AXI_HP0_ARBURST (dram.ar_burst),//S_AXI_HP0_ARBURST : in STD_LOGIC_VECTOR ( 1 downto 0 );
    .S_AXI_HP0_ARLOCK ({1'b0,dram.ar_lock}),//S_AXI_HP0_ARLOCK : in STD_LOGIC_VECTOR ( 1 downto 0 );
    .S_AXI_HP0_ARSIZE (dram.ar_size),//S_AXI_HP0_ARSIZE : in STD_LOGIC_VECTOR ( 2 downto 0 );
    .S_AXI_HP0_AWBURST (dram.aw_burst),//S_AXI_HP0_AWBURST : in STD_LOGIC_VECTOR ( 1 downto 0 );
    .S_AXI_HP0_AWLOCK ({1'b0,dram.aw_lock}),//S_AXI_HP0_AWLOCK : in STD_LOGIC_VECTOR ( 1 downto 0 );
    .S_AXI_HP0_AWSIZE (dram.aw_size),//S_AXI_HP0_AWSIZE : in STD_LOGIC_VECTOR ( 2 downto 0 );
    .S_AXI_HP0_ARPROT (dram.ar_prot),//S_AXI_HP0_ARPROT : in STD_LOGIC_VECTOR ( 2 downto 0 );
    .S_AXI_HP0_AWPROT (dram.aw_prot),//S_AXI_HP0_AWPROT : in STD_LOGIC_VECTOR ( 2 downto 0 );
    .S_AXI_HP0_ARADDR (saxibram_araddr),//S_AXI_HP0_ARADDR : in STD_LOGIC_VECTOR ( 31 downto 0 );
    .S_AXI_HP0_AWADDR (saxibram_awaddr),//S_AXI_HP0_AWADDR : in STD_LOGIC_VECTOR ( 31 downto 0 );
    .S_AXI_HP0_ARCACHE (dram.ar_cache),//S_AXI_HP0_ARCACHE : in STD_LOGIC_VECTOR ( 3 downto 0 );
    .S_AXI_HP0_ARLEN (dram.ar_len),//S_AXI_HP0_ARLEN : in STD_LOGIC_VECTOR ( 3 downto 0 );
    .S_AXI_HP0_ARQOS (dram.ar_qos),//S_AXI_HP0_ARQOS : in STD_LOGIC_VECTOR ( 3 downto 0 );
    .S_AXI_HP0_AWCACHE (dram.aw_cache),//S_AXI_HP0_AWCACHE : in STD_LOGIC_VECTOR ( 3 downto 0 );
    .S_AXI_HP0_AWLEN (dram.aw_len),//S_AXI_HP0_AWLEN : in STD_LOGIC_VECTOR ( 3 downto 0 );
    .S_AXI_HP0_AWQOS (dram.aw_qos),//S_AXI_HP0_AWQOS : in STD_LOGIC_VECTOR ( 3 downto 0 );
    .S_AXI_HP0_ARID ({1'b0,dram.ar_id}),//S_AXI_HP0_ARID : in STD_LOGIC_VECTOR ( 5 downto 0 );
    .S_AXI_HP0_AWID ({1'b0,dram.aw_id}),//S_AXI_HP0_AWID : in STD_LOGIC_VECTOR ( 5 downto 0 );
    .S_AXI_HP0_WID ({1'b0,dram.aw_id}),//S_AXI_HP0_WID : in STD_LOGIC_VECTOR ( 5 downto 0 );
    .S_AXI_HP0_WDATA (dram.w_data),//S_AXI_HP0_WDATA : in STD_LOGIC_VECTOR ( 63 downto 0 );
    .S_AXI_HP0_WSTRB (dram.w_strb),//S_AXI_HP0_WSTRB : in STD_LOGIC_VECTOR ( 7 downto 0 );

//FPGA EXTERNAL PORT
    .MIO (mio),//MIO : inout STD_LOGIC_VECTOR ( 53 downto 0 );

    .DDR_Addr(DDR_addr[14:0]),//DDR_Addr : inout STD_LOGIC_VECTOR ( 14 downto 0 );
    .DDR_BankAddr(DDR_ba[2:0]),//DDR_BankAddr : inout STD_LOGIC_VECTOR ( 2 downto 0 );
    .DDR_CAS_n(DDR_cas_n),//DDR_CAS_n : inout STD_LOGIC;
    .DDR_CKE(DDR_cke),//DDR_CKE : inout STD_LOGIC;
    .DDR_CS_n(DDR_cs_n),//DDR_CS_n : inout STD_LOGIC;
    .DDR_Clk(DDR_ck_p),//DDR_Clk : inout STD_LOGIC;
    .DDR_Clk_n(DDR_ck_n),//DDR_Clk_n : inout STD_LOGIC;
    .DDR_DM(DDR_dm[3:0]),//DDR_DM : inout STD_LOGIC_VECTOR ( 3 downto 0 );
    .DDR_DQ(DDR_dq[31:0]),//DDR_DQ : inout STD_LOGIC_VECTOR ( 31 downto 0 );
    .DDR_DQS(DDR_dqs_p[3:0]),//DDR_DQS : inout STD_LOGIC_VECTOR ( 3 downto 0 ); 
    .DDR_DQS_n(DDR_dqs_n[3:0]),//DDR_DQS_n : inout STD_LOGIC_VECTOR ( 3 downto 0 );
    .DDR_DRSTB(DDR_reset_n),//DDR_DRSTB : inout STD_LOGIC;
    .DDR_ODT(DDR_odt),//DDR_ODT : inout STD_LOGIC;
    .DDR_RAS_n(DDR_ras_n),//DDR_RAS_n : inout STD_LOGIC;
    .DDR_VRN(ddr_vrn),//DDR_VRN : inout STD_LOGIC;
    .DDR_VRP(ddr_vrp),//DDR_VRP : inout STD_LOGIC;
    .DDR_WEB(DDR_we_n),//DDR_WEB : inout STD_LOGIC;

    .PS_CLK(ps_clk),
    .PS_PORB(ps_porb),
    .PS_SRSTB(ps_srstb)
  );
  
`else

xlnx_blk_mem_gen i_xlnx_blk_mem_gen (

    .rsta_busy (      ),
    .rstb_busy (      ),
    .s_aclk ( clk ),
    .s_aresetn ( ndmreset_n  ),
    .s_axi_awid ( dram.aw_id ),
    .s_axi_awaddr ( saxibram_awaddr ),
    .s_axi_awlen ( dram.aw_len ),
    .s_axi_awsize ( dram.aw_size ),
    .s_axi_awburst ( dram.aw_burst ),
    .s_axi_awvalid ( dram.aw_valid ),
    .s_axi_awready ( dram.aw_ready ),
    .s_axi_wdata ( dram.w_data ),
    .s_axi_wstrb ( dram.w_strb ),
    .s_axi_wlast ( dram.w_last ),
    .s_axi_wvalid ( dram.w_valid ),
    .s_axi_wready ( dram.w_ready ),
    .s_axi_bid ( dram.b_id ),
    .s_axi_bresp ( dram.b_resp ),
    .s_axi_bvalid ( dram.b_valid ),
    .s_axi_bready ( dram.b_ready ),
    .s_axi_arid ( dram.ar_id ),
    .s_axi_araddr ( saxibram_araddr ),
    .s_axi_arlen ( dram.ar_len ),
    .s_axi_arsize ( dram.ar_size ),
    .s_axi_arburst( dram.ar_burst ),
    .s_axi_arvalid ( dram.ar_valid ),
    .s_axi_arready ( dram.ar_ready ),
    .s_axi_rid ( dram.r_id ),
    .s_axi_rdata ( dram.r_data ),
    .s_axi_rresp ( dram.r_resp ),
    .s_axi_rlast ( dram.r_last ),
    .s_axi_rvalid ( dram.r_valid ),
    .s_axi_rready ( dram.r_ready )
  );

`endif  

endmodule

