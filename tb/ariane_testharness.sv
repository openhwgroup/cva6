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
// Description: Test-harness for Ariane
//              Instantiates an AXI-Bus and memories

`include "axi/assign.svh"

module ariane_testharness #(
  parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
  parameter bit          InclSimDTM        = 1'b1,
  parameter int unsigned NUM_WORDS         = 2**25,         // memory size
  parameter bit          StallRandomOutput = 1'b0,
  parameter bit          StallRandomInput  = 1'b0
) (
  input  logic                           clk_i,
  input  logic                           rtc_i,
  input  logic                           rst_ni,
  output logic [31:0]                    exit_o
);

  // disable test-enable
  logic        test_en;
  logic        ndmreset;
  logic        ndmreset_n;
  logic        debug_req_core;

  int          jtag_enable;
  logic        init_done;
  logic [31:0] jtag_exit, dmi_exit;

  logic        jtag_TCK;
  logic        jtag_TMS;
  logic        jtag_TDI;
  logic        jtag_TRSTn;
  logic        jtag_TDO_data;
  logic        jtag_TDO_driven;

  logic        debug_req_valid;
  logic        debug_req_ready;
  logic        debug_resp_valid;
  logic        debug_resp_ready;

  logic        jtag_req_valid;
  //logic [6:0]  jtag_req_bits_addr;
  //logic [1:0]  jtag_req_bits_op;
  //logic [31:0] jtag_req_bits_data;
  logic        jtag_resp_ready;
  logic        jtag_resp_valid;

  logic        dmi_req_valid;
  logic        dmi_resp_ready;
  logic        dmi_resp_valid;

  dm::dmi_req_t  jtag_dmi_req;
  dm::dmi_req_t  dmi_req;

  dm::dmi_req_t  debug_req;
  dm::dmi_resp_t debug_resp;

  assign test_en = 1'b0;

  rstgen i_rstgen_main (
    .clk_i        ( clk_i                ),
    .rst_ni       ( rst_ni & (~ndmreset) ),
    .test_mode_i  ( test_en              ),
    .rst_no       ( ndmreset_n           ),
    .init_no      (                      ) // keep open
  );

  // axi busses to the crossbar
  ariane_axi::req_t  [ariane_soc::NrSlaves-1:0] slv_ports_req;
  ariane_axi::resp_t [ariane_soc::NrSlaves-1:0] slv_ports_resp;

  ariane_axi::req_slv_t  [ariane_soc::NoSocAxiSlaves-1:0] mst_ports_req;
  ariane_axi::resp_slv_t [ariane_soc::NoSocAxiSlaves-1:0] mst_ports_resp;

  // ---------------
  // Debug
  // ---------------
  assign init_done = rst_ni;

  initial begin
    if (!$value$plusargs("jtag_rbb_enable=%b", jtag_enable)) jtag_enable = 'h0;
  end

  // debug if MUX
  assign debug_req_valid     = (jtag_enable[0]) ? jtag_req_valid     : dmi_req_valid;
  assign debug_resp_ready    = (jtag_enable[0]) ? jtag_resp_ready    : dmi_resp_ready;
  assign debug_req           = (jtag_enable[0]) ? jtag_dmi_req       : dmi_req;
  assign exit_o              = (jtag_enable[0]) ? jtag_exit          : dmi_exit;
  assign jtag_resp_valid     = (jtag_enable[0]) ? debug_resp_valid   : 1'b0;
  assign dmi_resp_valid      = (jtag_enable[0]) ? 1'b0               : debug_resp_valid;

  // SiFive's SimJTAG Module
  // Converts to DPI calls
  SimJTAG i_SimJTAG (
    .clock                ( clk_i                ),
    .reset                ( ~rst_ni              ),
    .enable               ( jtag_enable[0]       ),
    .init_done            ( init_done            ),
    .jtag_TCK             ( jtag_TCK             ),
    .jtag_TMS             ( jtag_TMS             ),
    .jtag_TDI             ( jtag_TDI             ),
    .jtag_TRSTn           ( jtag_TRSTn           ),
    .jtag_TDO_data        ( jtag_TDO_data        ),
    .jtag_TDO_driven      ( jtag_TDO_driven      ),
    .exit                 ( jtag_exit            )
  );

  dmi_jtag i_dmi_jtag (
    .clk_i            ( clk_i           ),
    .rst_ni           ( rst_ni          ),
    .testmode_i       ( test_en         ),
    .dmi_req_o        ( jtag_dmi_req    ),
    .dmi_req_valid_o  ( jtag_req_valid  ),
    .dmi_req_ready_i  ( debug_req_ready ),
    .dmi_resp_i       ( debug_resp      ),
    .dmi_resp_ready_o ( jtag_resp_ready ),
    .dmi_resp_valid_i ( jtag_resp_valid ),
    .dmi_rst_no       (                 ), // not connected
    .tck_i            ( jtag_TCK        ),
    .tms_i            ( jtag_TMS        ),
    .trst_ni          ( jtag_TRSTn      ),
    .td_i             ( jtag_TDI        ),
    .td_o             ( jtag_TDO_data   ),
    .tdo_oe_o         ( jtag_TDO_driven )
  );

  // SiFive's SimDTM Module
  // Converts to DPI calls
  logic [1:0] debug_req_bits_op;
  assign dmi_req.op = dm::dtm_op_e'(debug_req_bits_op);

  if (InclSimDTM) begin : gen_SimDTM
    SimDTM i_SimDTM (
      .clk                  ( clk_i                 ),
      .reset                ( ~rst_ni               ),
      .debug_req_valid      ( dmi_req_valid         ),
      .debug_req_ready      ( debug_req_ready       ),
      .debug_req_bits_addr  ( dmi_req.addr          ),
      .debug_req_bits_op    ( debug_req_bits_op     ),
      .debug_req_bits_data  ( dmi_req.data          ),
      .debug_resp_valid     ( dmi_resp_valid        ),
      .debug_resp_ready     ( dmi_resp_ready        ),
      .debug_resp_bits_resp ( debug_resp.resp       ),
      .debug_resp_bits_data ( debug_resp.data       ),
      .exit                 ( dmi_exit              )
    );
  end else begin : gen_no_SimDTM
    assign dmi_req_valid = '0;
    assign debug_req_bits_op = '0;
    assign dmi_exit = 1'b0;
  end

  // this delay window allows the core to read and execute init code
  // from the bootrom before the first debug request can interrupt
  // core. this is needed in cases where an fsbl is involved that
  // expects a0 and a1 to be initialized with the hart id and a
  // pointer to the dev tree, respectively.
  localparam int unsigned DmiDelCycles = 500;

  logic debug_req_core_ungtd;
  int dmi_del_cnt_d, dmi_del_cnt_q;

  assign dmi_del_cnt_d  = (dmi_del_cnt_q) ? dmi_del_cnt_q - 1 : 0;
  assign debug_req_core = (dmi_del_cnt_q) ? 1'b0 : debug_req_core_ungtd;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_dmi_del_cnt
    if(!rst_ni) begin
      dmi_del_cnt_q <= DmiDelCycles;
    end else begin
      dmi_del_cnt_q <= dmi_del_cnt_d;
    end
  end

  logic                dm_slave_req;
  logic                dm_slave_we;
  logic [64-1:0]       dm_slave_addr;
  logic [64/8-1:0]     dm_slave_be;
  logic [64-1:0]       dm_slave_wdata;
  logic [64-1:0]       dm_slave_rdata;

  logic                dm_master_req;
  logic [64-1:0]       dm_master_add;
  logic                dm_master_we;
  logic [64-1:0]       dm_master_wdata;
  logic [64/8-1:0]     dm_master_be;
  logic                dm_master_gnt;
  logic                dm_master_r_valid;
  logic [64-1:0]       dm_master_r_rdata;

  // debug module
  dm_top #(
    .NrHarts              ( 1                           ),
    .BusWidth             ( AXI_DATA_WIDTH              ),
    .SelectableHarts      ( 1'b1                        )
  ) i_dm_top (
    .clk_i                ( clk_i                       ),
    .rst_ni               ( rst_ni                      ), // PoR
    .testmode_i           ( test_en                     ),
    .ndmreset_o           ( ndmreset                    ),
    .dmactive_o           (                             ), // active debug session
    .debug_req_o          ( debug_req_core_ungtd        ),
    .unavailable_i        ( '0                          ),
    .hartinfo_i           ( {ariane_pkg::DebugHartInfo} ),
    .slave_req_i          ( dm_slave_req                ),
    .slave_we_i           ( dm_slave_we                 ),
    .slave_addr_i         ( dm_slave_addr               ),
    .slave_be_i           ( dm_slave_be                 ),
    .slave_wdata_i        ( dm_slave_wdata              ),
    .slave_rdata_o        ( dm_slave_rdata              ),
    .master_req_o         ( dm_master_req               ),
    .master_add_o         ( dm_master_add               ),
    .master_we_o          ( dm_master_we                ),
    .master_wdata_o       ( dm_master_wdata             ),
    .master_be_o          ( dm_master_be                ),
    .master_gnt_i         ( dm_master_gnt               ),
    .master_r_valid_i     ( dm_master_r_valid           ),
    .master_r_rdata_i     ( dm_master_r_rdata           ),
    .dmi_rst_ni           ( rst_ni                      ),
    .dmi_req_valid_i      ( debug_req_valid             ),
    .dmi_req_ready_o      ( debug_req_ready             ),
    .dmi_req_i            ( debug_req                   ),
    .dmi_resp_valid_o     ( debug_resp_valid            ),
    .dmi_resp_ready_i     ( debug_resp_ready            ),
    .dmi_resp_o           ( debug_resp                  )
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) dm_bus ();

  `AXI_ASSIGN_FROM_REQ( dm_bus,                             mst_ports_req[ariane_soc::AxiDebug] )
  `AXI_ASSIGN_TO_RESP ( mst_ports_resp[ariane_soc::AxiDebug] , dm_bus                           )

  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) i_dm_axi2mem (
    .clk_i      ( clk_i                     ),
    .rst_ni     ( rst_ni                    ),
    .slave      ( dm_bus                    ),
    .req_o      ( dm_slave_req              ),
    .we_o       ( dm_slave_we               ),
    .addr_o     ( dm_slave_addr             ),
    .be_o       ( dm_slave_be               ),
    .data_o     ( dm_slave_wdata            ),
    .data_i     ( dm_slave_rdata            )
  );

  axi_adapter #(
    .DATA_WIDTH            ( AXI_DATA_WIDTH            )
  ) i_dm_axi_master (
    .clk_i                 ( clk_i                     ),
    .rst_ni                ( rst_ni                    ),
    .req_i                 ( dm_master_req             ),
    .type_i                ( ariane_axi::SINGLE_REQ    ),
    .gnt_o                 ( dm_master_gnt             ),
    .gnt_id_o              (                           ),
    .addr_i                ( dm_master_add             ),
    .we_i                  ( dm_master_we              ),
    .wdata_i               ( dm_master_wdata           ),
    .be_i                  ( dm_master_be              ),
    .size_i                ( 2'b11                     ), // always do 64bit here and use byte enables to gate
    .id_i                  ( '0                        ),
    .valid_o               ( dm_master_r_valid         ),
    .rdata_o               ( dm_master_r_rdata         ),
    .id_o                  (                           ),
    .critical_word_o       (                           ),
    .critical_word_valid_o (                           ),
    .axi_req_o             ( slv_ports_req[1]          ),
    .axi_resp_i            ( slv_ports_resp[1]         )
  );


  // ---------------
  // ROM
  // ---------------
  logic                         rom_req;
  logic [AXI_ADDRESS_WIDTH-1:0] rom_addr;
  logic [AXI_DATA_WIDTH-1:0]    rom_rdata;

  AXI_BUS #(
      .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
      .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) rom_bus();

  `AXI_ASSIGN_FROM_REQ ( rom_bus,                         mst_ports_req [ariane_soc::AxiRom] )
  `AXI_ASSIGN_TO_RESP  ( mst_ports_resp[ariane_soc::AxiRom], rom_bus                         )

  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) i_axi2rom (
    .clk_i  ( clk_i      ),
    .rst_ni ( ndmreset_n ),
    .slave  ( rom_bus    ),
    .req_o  ( rom_req    ),
    .we_o   (            ),
    .addr_o ( rom_addr   ),
    .be_o   (            ),
    .data_o (            ),
    .data_i ( rom_rdata  )
  );

  bootrom i_bootrom (
    .clk_i      ( clk_i     ),
    .req_i      ( rom_req   ),
    .addr_i     ( rom_addr  ),
    .rdata_o    ( rom_rdata )
  );

  // ------------------------------
  // Memory + Exclusive Access
  // ------------------------------
  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) dram_atop ();


  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) dram();

  logic                         req;
  logic                         we;
  logic [AXI_ADDRESS_WIDTH-1:0] addr;
  logic [AXI_DATA_WIDTH/8-1:0]  be;
  logic [AXI_DATA_WIDTH-1:0]    wdata;
  logic [AXI_DATA_WIDTH-1:0]    rdata;

  `AXI_ASSIGN_FROM_REQ ( dram_atop,                        mst_ports_req [ariane_soc::AxiDram] )
  `AXI_ASSIGN_TO_RESP  ( mst_ports_resp[ariane_soc::AxiDram], dram_atop                        )

  axi_riscv_atomics_wrap #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           ),
    .AXI_MAX_WRITE_TXNS ( 1  ),
    .RISCV_WORD_WIDTH   ( 64 )
  ) i_axi_riscv_atomics (
    .clk_i,
    .rst_ni ( ndmreset_n  ),
    .slv    ( dram_atop   ),
    .mst    ( dram        )
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) dram_delayed();

  ariane_axi::req_slv_t  dram_req,  dram_delayed_req;
  ariane_axi::resp_slv_t dram_resp, dram_delayed_resp;

  `AXI_ASSIGN_TO_REQ    ( dram_req, dram      )
  `AXI_ASSIGN_FROM_RESP ( dram,     dram_resp )

  axi_delayer #(
    .aw_chan_t         ( ariane_axi::aw_chan_slv_t ),
    .w_chan_t          ( ariane_axi::w_chan_t      ),
    .b_chan_t          ( ariane_axi::b_chan_slv_t  ),
    .ar_chan_t         ( ariane_axi::ar_chan_slv_t ),
    .r_chan_t          ( ariane_axi::r_chan_slv_t  ),
    .req_t             ( ariane_axi::req_slv_t     ),
    .resp_t            ( ariane_axi::resp_slv_t    ),
    .StallRandomOutput ( StallRandomOutput         ),
    .StallRandomInput  ( StallRandomInput          ),
    .FixedDelayInput   ( 0                         ),
    .FixedDelayOutput  ( 0                         )
  ) i_axi_delayer (
    .clk_i      ( clk_i             ),
    .rst_ni     ( ndmreset_n        ),
    .slv_req_i  ( dram_req          ),
    .slv_resp_o ( dram_resp         ),
    .mst_req_o  ( dram_delayed_req  ),
    .mst_resp_i ( dram_delayed_resp )
  );

  `AXI_ASSIGN_FROM_REQ ( dram_delayed,      dram_delayed_req )
  `AXI_ASSIGN_TO_RESP  ( dram_delayed_resp, dram_delayed     )

  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) i_axi2mem (
    .clk_i  ( clk_i        ),
    .rst_ni ( ndmreset_n   ),
    .slave  ( dram_delayed ),
    .req_o  ( req          ),
    .we_o   ( we           ),
    .addr_o ( addr         ),
    .be_o   ( be           ),
    .data_o ( wdata        ),
    .data_i ( rdata        )
  );

  sram #(
    .DATA_WIDTH ( AXI_DATA_WIDTH ),
    .NUM_WORDS  ( NUM_WORDS      )
  ) i_sram (
    .clk_i      ( clk_i                                                                       ),
    .rst_ni     ( rst_ni                                                                      ),
    .req_i      ( req                                                                         ),
    .we_i       ( we                                                                          ),
    .addr_i     ( addr[$clog2(NUM_WORDS)-1+$clog2(AXI_DATA_WIDTH/8):$clog2(AXI_DATA_WIDTH/8)] ),
    .wdata_i    ( wdata                                                                       ),
    .be_i       ( be                                                                          ),
    .rdata_o    ( rdata                                                                       )
  );

  // ---------------
  // AXI Xbar
  // ---------------
  axi_xbar #(
    .Cfg            ( ariane_soc::XbarCfg       ),
    .slv_aw_chan_t  ( ariane_axi::aw_chan_t     ),
    .mst_aw_chan_t  ( ariane_axi::aw_chan_slv_t ),
    .w_chan_t       ( ariane_axi::w_chan_t      ),
    .slv_b_chan_t   ( ariane_axi::b_chan_t      ),
    .mst_b_chan_t   ( ariane_axi::b_chan_slv_t  ),
    .slv_ar_chan_t  ( ariane_axi::ar_chan_t     ),
    .mst_ar_chan_t  ( ariane_axi::ar_chan_slv_t ),
    .slv_r_chan_t   ( ariane_axi::r_chan_t      ),
    .mst_r_chan_t   ( ariane_axi::r_chan_slv_t  ),
    .slv_req_t      ( ariane_axi::req_t         ),
    .slv_resp_t     ( ariane_axi::resp_t        ),
    .mst_req_t      ( ariane_axi::req_slv_t     ),
    .mst_resp_t     ( ariane_axi::resp_slv_t    ),
    .rule_t         ( axi_pkg::xbar_rule_64_t   )
  ) i_axi_xbar (
    .clk_i  ( clk_i      ),
    .rst_ni ( rst_ni     ),
    .test_i ( test_en    ),
    // slave ports, connect here the master modules
    .slv_ports_req_i  ( slv_ports_req  ),
    .slv_ports_resp_o ( slv_ports_resp ),
    // master ports, connect here the slave modules
    .mst_ports_req_o  ( mst_ports_req  ),
    .mst_ports_resp_i ( mst_ports_resp ),
    // addr map input
    .addr_map_i       ( ariane_soc::AxiAddrMap        ),
    .en_default_mst_port_i ( '0        ),
    .default_mst_port_i    ( '0        )
  );

  // ---------------
  // CLINT
  // ---------------
  logic ipi;
  logic timer_irq;

  clint #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .NR_CORES       ( 1                        )
  ) i_clint (
    .clk_i       ( clk_i                                ),
    .rst_ni      ( ndmreset_n                           ),
    .testmode_i  ( test_en                              ),
    .axi_req_i   ( mst_ports_req [ariane_soc::AxiClint] ),
    .axi_resp_o  ( mst_ports_resp[ariane_soc::AxiClint] ),
    .rtc_i       ( rtc_i                                ),
    .timer_irq_o ( timer_irq                            ),
    .ipi_o       ( ipi                                  )
  );

  // ---------------
  // Peripherals
  // ---------------
  logic tx, rx;
  logic [1:0] irqs;

//  AXI_BUS #(
//      .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
//      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
//      .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
//      .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
//  ) apb_peripheral_bus();
//  `AXI_ASSIGN_FROM_REQ ( apb_peripheral_bus,             mst_ports_req[ariane_soc::AxiApbPeriph] )
//  `AXI_ASSIGN_TO_RESP  ( mst_ports_resp[ariane_soc::AxiApbPeriph], apb_peripheral_bus            )

//  AXI_BUS #(
//      .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
//      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
//      .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
//      .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
//  ) plic_bus();
//  `AXI_ASSIGN_FROM_REQ ( plic_bus,                         mst_ports_req[ariane_soc::PLIC] )
//  `AXI_ASSIGN_TO_RESP  ( mst_ports_resp[ariane_soc::PLIC], plic_bus                        )
//  AXI_BUS #(
//      .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
//      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
//      .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
//      .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
//  ) uart_bus();
//  `AXI_ASSIGN_FROM_REQ ( uart_bus,                         mst_ports_req[ariane_soc::UART] )
//  `AXI_ASSIGN_TO_RESP  ( mst_ports_resp[ariane_soc::UART], uart_bus                        )
  AXI_BUS #(
      .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
      .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) spi_bus();
  `AXI_ASSIGN_FROM_REQ(spi_bus, mst_ports_req[ariane_soc::AxiSpi])
  `AXI_ASSIGN_TO_RESP(mst_ports_resp[ariane_soc::AxiSpi], spi_bus)
  AXI_BUS #(
      .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
      .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) ethernet_bus();
  `AXI_ASSIGN_FROM_REQ(ethernet_bus, mst_ports_req[ariane_soc::AxiEthernet])
  `AXI_ASSIGN_TO_RESP(mst_ports_resp[ariane_soc::AxiEthernet], ethernet_bus)
  AXI_BUS #(
      .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
      .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) gpio_bus();
  `AXI_ASSIGN_FROM_REQ(gpio_bus, mst_ports_req[ariane_soc::AxiGpio])
  `AXI_ASSIGN_TO_RESP(mst_ports_resp[ariane_soc::AxiGpio], gpio_bus)

  // from file `fpga/src/ariane_peripherals_xilinx`
  ariane_peripherals #(
    .AxiAddrWidth ( AXI_ADDRESS_WIDTH        ),
    .AxiDataWidth ( AXI_DATA_WIDTH           ),
    .AxiIdWidth   ( ariane_soc::IdWidthSlave ),
`ifndef VERILATOR
  // disable UART when using Spike, as we need to rely on the mockuart
  `ifdef SPIKE_TANDEM
    .InclUART     ( 1'b0                     ),
  `else
    .InclUART     ( 1'b1                     ),
  `endif
`else
    .InclUART     ( 1'b0                     ),
`endif
    .InclSPI      ( 1'b0                     ),
    .InclEthernet ( 1'b0                     ),
    .InclTimer    ( 1'b1                     )
  ) i_ariane_peripherals (
    .clk_i             ( clk_i                                    ),
    .clk_200MHz_i      ( 1'b0                                     ), // not used in tb (eth clk)
    .rst_ni            ( ndmreset_n                               ),
    .spi               ( spi_bus                                  ),
    .gpio              ( gpio_bus                                 ),
    .ethernet          ( ethernet_bus                             ),
    .periph_axi_req_i  ( mst_ports_req[ariane_soc::AxiApbPeriph]  ),
    .periph_axi_resp_o ( mst_ports_resp[ariane_soc::AxiApbPeriph] ),
    .irq_o             ( irqs                                     ),
    .rx_i              ( rx                                       ),
    .tx_o              ( tx                                       ),
    .eth_clk_i         ( '0                                       ), // not used in tb
    .eth_rxck          ( '0                                       ),
    .eth_rxctl         ( '0                                       ),
    .eth_rxd           ( '0                                       ),
    .eth_txck          ( /*not used in tb*/                       ), // not used in tb
    .eth_txctl         ( /*not used in tb*/                       ), // not used in tb
    .eth_txd           ( /*not used in tb*/                       ), // not used in tb
    .eth_rst_n         ( /*not used in tb*/                       ), // not used in tb
    .phy_tx_clk_i      ( '0                                       ), // not used in tb
    .eth_mdio          ( /*not used in tb*/                       ),
    .eth_mdc           ( /*not used in tb*/                       ),
    .spi_clk_o         ( /*not used in tb*/                       ),
    .spi_mosi          ( /*not used in tb*/                       ),
    .spi_miso          ( '0                                       ), // not used in tb
    .spi_ss            ( /*not used in tb*/                       ),
    .leds_o            ( /*not used in tb*/                       ),
    .dip_switches_i    ( '0                                       )  // not used in tb
  );

  uart_bus #(.BAUD_RATE(115200), .PARITY_EN(0)) i_uart_bus (.rx(tx), .tx(rx), .rx_en(1'b1));

  // ---------------
  // Core
  // ---------------

  ariane #(
    .ArianeCfg  ( ariane_soc::ArianeSocCfg )
  ) i_ariane (
    .clk_i                ( clk_i               ),
    .rst_ni               ( ndmreset_n          ),
    .boot_addr_i          ( ariane_soc::ROMBase ), // start fetching from ROM
    .hart_id_i            ( '0                  ),
    .irq_i                ( irqs                ),
    .ipi_i                ( ipi                 ),
    .time_irq_i           ( timer_irq           ),
// Disable Debug when simulating with Spike
`ifdef SPIKE_TANDEM
    .debug_req_i          ( 1'b0                ),
`else
    .debug_req_i          ( debug_req_core      ),
`endif
    .axi_req_o            ( slv_ports_req[0]    ),
    .axi_resp_i           ( slv_ports_resp[0]   )
  );

  // -------------
  // Simulation Helper Functions
  // -------------
  // check for response errors
  always_ff @(posedge clk_i) begin : p_assert
    if (slv_ports_req[0].r_ready &&
      slv_ports_resp[0].r_valid &&
      slv_ports_resp[0].r.resp inside {axi_pkg::RESP_DECERR, axi_pkg::RESP_SLVERR}) begin
      $warning("R Response Errored");
    end
    if (slv_ports_req[0].b_ready &&
      slv_ports_resp[0].b_valid &&
      slv_ports_resp[0].b.resp inside {axi_pkg::RESP_DECERR, axi_pkg::RESP_SLVERR}) begin
      $warning("B Response Errored");
    end
  end

`ifdef AXI_SVA
  // AXI 4 Assertion IP integration - You will need to get your own copy of this IP if you want
  // to use it
  Axi4PC #(
    .DATA_WIDTH(ariane_axi::DataWidth),
    .WID_WIDTH(ariane_soc::IdWidthSlave),
    .RID_WIDTH(ariane_soc::IdWidthSlave),
    .AWUSER_WIDTH(ariane_axi::UserWidth),
    .WUSER_WIDTH(ariane_axi::UserWidth),
    .BUSER_WIDTH(ariane_axi::UserWidth),
    .ARUSER_WIDTH(ariane_axi::UserWidth),
    .RUSER_WIDTH(ariane_axi::UserWidth),
    .ADDR_WIDTH(ariane_axi::AddrWidth)
  ) i_Axi4PC (
    .ACLK(clk_i),
    .ARESETn(ndmreset_n),
    .AWID(dram.aw_id),
    .AWADDR(dram.aw_addr),
    .AWLEN(dram.aw_len),
    .AWSIZE(dram.aw_size),
    .AWBURST(dram.aw_burst),
    .AWLOCK(dram.aw_lock),
    .AWCACHE(dram.aw_cache),
    .AWPROT(dram.aw_prot),
    .AWQOS(dram.aw_qos),
    .AWREGION(dram.aw_region),
    .AWUSER(dram.aw_user),
    .AWVALID(dram.aw_valid),
    .AWREADY(dram.aw_ready),
    .WLAST(dram.w_last),
    .WDATA(dram.w_data),
    .WSTRB(dram.w_strb),
    .WUSER(dram.w_user),
    .WVALID(dram.w_valid),
    .WREADY(dram.w_ready),
    .BID(dram.b_id),
    .BRESP(dram.b_resp),
    .BUSER(dram.b_user),
    .BVALID(dram.b_valid),
    .BREADY(dram.b_ready),
    .ARID(dram.ar_id),
    .ARADDR(dram.ar_addr),
    .ARLEN(dram.ar_len),
    .ARSIZE(dram.ar_size),
    .ARBURST(dram.ar_burst),
    .ARLOCK(dram.ar_lock),
    .ARCACHE(dram.ar_cache),
    .ARPROT(dram.ar_prot),
    .ARQOS(dram.ar_qos),
    .ARREGION(dram.ar_region),
    .ARUSER(dram.ar_user),
    .ARVALID(dram.ar_valid),
    .ARREADY(dram.ar_ready),
    .RID(dram.r_id),
    .RLAST(dram.r_last),
    .RDATA(dram.r_data),
    .RRESP(dram.r_resp),
    .RUSER(dram.r_user),
    .RVALID(dram.r_valid),
    .RREADY(dram.r_ready),
    .CACTIVE('0),
    .CSYSREQ('0),
    .CSYSACK('0)
  );
`endif
endmodule
