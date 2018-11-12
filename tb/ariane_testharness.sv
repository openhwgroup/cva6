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

module ariane_testharness #(
    parameter logic [63:0] CACHE_START_ADDR  = 64'h8000_0000, // address on which to decide whether the request is cache-able or not
    parameter int unsigned AXI_ID_WIDTH      = 2,
    parameter int unsigned AXI_USER_WIDTH    = 1,
    parameter int unsigned AXI_ADDRESS_WIDTH = 64,
    parameter int unsigned AXI_DATA_WIDTH    = 64,
    parameter bit          InclSimDTM        = 1'b0,
    parameter int unsigned NUM_WORDS         = 2**25          // memory size
)(
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
    logic [6:0]  jtag_req_bits_addr;
    logic [1:0]  jtag_req_bits_op;
    logic [31:0] jtag_req_bits_data;
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
    assign ndmreset_n = ~ndmreset ;

    localparam NB_SLAVE = 4;

    localparam AXI_ID_WIDTH_SLAVES = AXI_ID_WIDTH + $clog2(NB_SLAVE);

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) slave[NB_SLAVE-1:0]();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_SLAVES ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH      )
    ) master[ariane_soc::NB_PERIPHERALS-1:0]();

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
    assign dmi_req.op = dm::dtm_op_t'(debug_req_bits_op);

    if (InclSimDTM) begin
        SimDTM i_SimDTM (
            .clk                  ( clk_i                ),
            .reset                ( ~rst_ni              ),
            .debug_req_valid      ( dmi_req_valid        ),
            .debug_req_ready      ( debug_req_ready      ),
            .debug_req_bits_addr  ( dmi_req.addr         ),
            .debug_req_bits_op    ( debug_req_bits_op    ),
            .debug_req_bits_data  ( dmi_req.data         ),
            .debug_resp_valid     ( dmi_resp_valid       ),
            .debug_resp_ready     ( dmi_resp_ready       ),
            .debug_resp_bits_resp ( debug_resp.resp      ),
            .debug_resp_bits_data ( debug_resp.data      ),
            .exit                 ( dmi_exit             )
        );
    end else begin
        assign dmi_req_valid = '0;
        assign debug_req_bits_op = '0;
        assign dmi_exit = 1'b0;
    end

    // debug module
    dm_top #(
        // current implementation only supports 1 hart
        .NrHarts              ( 1                    ),
        .AxiIdWidth           ( AXI_ID_WIDTH_SLAVES  ),
        .AxiAddrWidth         ( AXI_ADDRESS_WIDTH    ),
        .AxiDataWidth         ( AXI_DATA_WIDTH       ),
        .AxiUserWidth         ( AXI_USER_WIDTH       )
    ) i_dm_top (
        .clk_i                ( clk_i                     ),
        .rst_ni               ( rst_ni                    ), // PoR
        .testmode_i           ( test_en                   ),
        .ndmreset_o           ( ndmreset                  ),
        .dmactive_o           (                           ), // active debug session
        .debug_req_o          ( debug_req_core            ),
        .unavailable_i        ( '0                        ),
        .axi_master           ( slave[3]                  ),
        .axi_slave            ( master[ariane_soc::Debug] ),
        .dmi_rst_ni           ( rst_ni                    ),
        .dmi_req_valid_i      ( debug_req_valid           ),
        .dmi_req_ready_o      ( debug_req_ready           ),
        .dmi_req_i            ( debug_req                 ),
        .dmi_resp_valid_o     ( debug_resp_valid          ),
        .dmi_resp_ready_i     ( debug_resp_ready          ),
        .dmi_resp_o           ( debug_resp                )
    );

    // ---------------
    // ROM
    // ---------------
    logic                         rom_req;
    logic [AXI_ADDRESS_WIDTH-1:0] rom_addr;
    logic [AXI_DATA_WIDTH-1:0]    rom_rdata;

    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_SLAVES ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH      )
    ) i_axi2rom (
        .clk_i  ( clk_i                   ),
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
        .clk_i      ( clk_i     ),
        .req_i      ( rom_req   ),
        .addr_i     ( rom_addr  ),
        .rdata_o    ( rom_rdata )
    );

    // ---------------
    // Memory
    // ---------------

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_SLAVES ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH      )
    ) dram();

    logic                         req;
    logic                         we;
    logic [AXI_ADDRESS_WIDTH-1:0] addr;
    logic [AXI_DATA_WIDTH/8-1:0]  be;
    logic [AXI_DATA_WIDTH-1:0]    wdata;
    logic [AXI_DATA_WIDTH-1:0]    rdata;

    axi_pkg::aw_chan_t aw_chan_i;
    axi_pkg::w_chan_t  w_chan_i;
    axi_pkg::b_chan_t  b_chan_o;
    axi_pkg::ar_chan_t ar_chan_i;
    axi_pkg::r_chan_t  r_chan_o;
    axi_pkg::aw_chan_t aw_chan_o;
    axi_pkg::w_chan_t  w_chan_o;
    axi_pkg::b_chan_t  b_chan_i;
    axi_pkg::ar_chan_t ar_chan_o;
    axi_pkg::r_chan_t  r_chan_i;

    axi_delayer #(
        .aw_t              ( axi_pkg::aw_chan_t ),
        .w_t               ( axi_pkg::w_chan_t  ),
        .b_t               ( axi_pkg::b_chan_t  ),
        .ar_t              ( axi_pkg::ar_chan_t ),
        .r_t               ( axi_pkg::r_chan_t  ),
        .StallRandomOutput ( 1                  ),
        .StallRandomInput  ( 1                  ),
        .FixedDelayInput   ( 0                  ),
        .FixedDelayOutput  ( 0                  )
    ) i_axi_delayer (
        .clk_i      ( clk_i                             ),
        .rst_ni     ( ndmreset_n                        ),
        .aw_valid_i ( master[ariane_soc::DRAM].aw_valid ),
        .aw_chan_i  ( aw_chan_i                         ),
        .aw_ready_o ( master[ariane_soc::DRAM].aw_ready ),
        .w_valid_i  ( master[ariane_soc::DRAM].w_valid  ),
        .w_chan_i   ( w_chan_i                          ),
        .w_ready_o  ( master[ariane_soc::DRAM].w_ready  ),
        .b_valid_o  ( master[ariane_soc::DRAM].b_valid  ),
        .b_chan_o   ( b_chan_o                          ),
        .b_ready_i  ( master[ariane_soc::DRAM].b_ready  ),
        .ar_valid_i ( master[ariane_soc::DRAM].ar_valid ),
        .ar_chan_i  ( ar_chan_i                         ),
        .ar_ready_o ( master[ariane_soc::DRAM].ar_ready ),
        .r_valid_o  ( master[ariane_soc::DRAM].r_valid  ),
        .r_chan_o   ( r_chan_o                          ),
        .r_ready_i  ( master[ariane_soc::DRAM].r_ready  ),
        .aw_valid_o ( dram.aw_valid                     ),
        .aw_chan_o  ( aw_chan_o                         ),
        .aw_ready_i ( dram.aw_ready                     ),
        .w_valid_o  ( dram.w_valid                      ),
        .w_chan_o   ( w_chan_o                          ),
        .w_ready_i  ( dram.w_ready                      ),
        .b_valid_i  ( dram.b_valid                      ),
        .b_chan_i   ( b_chan_i                          ),
        .b_ready_o  ( dram.b_ready                      ),
        .ar_valid_o ( dram.ar_valid                     ),
        .ar_chan_o  ( ar_chan_o                         ),
        .ar_ready_i ( dram.ar_ready                     ),
        .r_valid_i  ( dram.r_valid                      ),
        .r_chan_i   ( r_chan_i                          ),
        .r_ready_o  ( dram.r_ready                      )
    );

    assign aw_chan_i.id = master[ariane_soc::DRAM].aw_id;
    assign aw_chan_i.addr = master[ariane_soc::DRAM].aw_addr;
    assign aw_chan_i.len = master[ariane_soc::DRAM].aw_len;
    assign aw_chan_i.size = master[ariane_soc::DRAM].aw_size;
    assign aw_chan_i.burst = master[ariane_soc::DRAM].aw_burst;
    assign aw_chan_i.lock = master[ariane_soc::DRAM].aw_lock;
    assign aw_chan_i.cache = master[ariane_soc::DRAM].aw_cache;
    assign aw_chan_i.prot = master[ariane_soc::DRAM].aw_prot;
    assign aw_chan_i.qos = master[ariane_soc::DRAM].aw_qos;
    assign aw_chan_i.region = master[ariane_soc::DRAM].aw_region;

    assign ar_chan_i.id = master[ariane_soc::DRAM].ar_id;
    assign ar_chan_i.addr = master[ariane_soc::DRAM].ar_addr;
    assign ar_chan_i.len = master[ariane_soc::DRAM].ar_len;
    assign ar_chan_i.size = master[ariane_soc::DRAM].ar_size;
    assign ar_chan_i.burst = master[ariane_soc::DRAM].ar_burst;
    assign ar_chan_i.lock = master[ariane_soc::DRAM].ar_lock;
    assign ar_chan_i.cache = master[ariane_soc::DRAM].ar_cache;
    assign ar_chan_i.prot = master[ariane_soc::DRAM].ar_prot;
    assign ar_chan_i.qos = master[ariane_soc::DRAM].ar_qos;
    assign ar_chan_i.region = master[ariane_soc::DRAM].ar_region;

    assign w_chan_i.data = master[ariane_soc::DRAM].w_data;
    assign w_chan_i.strb = master[ariane_soc::DRAM].w_strb;
    assign w_chan_i.last = master[ariane_soc::DRAM].w_last;

    assign master[ariane_soc::DRAM].r_id = r_chan_o.id;
    assign master[ariane_soc::DRAM].r_data = r_chan_o.data;
    assign master[ariane_soc::DRAM].r_resp = r_chan_o.resp;
    assign master[ariane_soc::DRAM].r_last = r_chan_o.last;

    assign master[ariane_soc::DRAM].b_id = b_chan_o.id;
    assign master[ariane_soc::DRAM].b_resp = b_chan_o.resp;


    assign dram.aw_id = aw_chan_o.id;
    assign dram.aw_addr = aw_chan_o.addr;
    assign dram.aw_len = aw_chan_o.len;
    assign dram.aw_size = aw_chan_o.size;
    assign dram.aw_burst = aw_chan_o.burst;
    assign dram.aw_lock = aw_chan_o.lock;
    assign dram.aw_cache = aw_chan_o.cache;
    assign dram.aw_prot = aw_chan_o.prot;
    assign dram.aw_qos = aw_chan_o.qos;
    assign dram.aw_region = aw_chan_o.region;
    assign dram.aw_user = master[ariane_soc::DRAM].aw_user;

    assign dram.ar_id = ar_chan_o.id;
    assign dram.ar_addr = ar_chan_o.addr;
    assign dram.ar_len = ar_chan_o.len;
    assign dram.ar_size = ar_chan_o.size;
    assign dram.ar_burst = ar_chan_o.burst;
    assign dram.ar_lock = ar_chan_o.lock;
    assign dram.ar_cache = ar_chan_o.cache;
    assign dram.ar_prot = ar_chan_o.prot;
    assign dram.ar_qos = ar_chan_o.qos;
    assign dram.ar_region = ar_chan_o.region;
    assign dram.ar_user = master[ariane_soc::DRAM].ar_user;

    assign dram.w_data = w_chan_o.data;
    assign dram.w_strb = w_chan_o.strb;
    assign dram.w_last = w_chan_o.last;
    assign dram.w_user = master[ariane_soc::DRAM].w_user;

    assign r_chan_i.id = dram.r_id;
    assign r_chan_i.data = dram.r_data;
    assign r_chan_i.resp = dram.r_resp;
    assign r_chan_i.last = dram.r_last;
    assign master[ariane_soc::DRAM].r_user = dram.r_user;

    assign b_chan_i.id = dram.b_id;
    assign b_chan_i.resp = dram.b_resp;
    assign master[ariane_soc::DRAM].b_user = dram.b_user;


    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_SLAVES ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH      )
    ) i_axi2mem (
        .clk_i  ( clk_i      ),
        .rst_ni ( ndmreset_n ),
        .slave  ( dram       ),
        .req_o  ( req        ),
        .we_o   ( we         ),
        .addr_o ( addr       ),
        .be_o   ( be         ),
        .data_o ( wdata      ),
        .data_i ( rdata      )
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
    axi_node_wrap_with_slices #(
        // three ports from Ariane (instruction, data and bypass)
        .NB_SLAVE           ( NB_SLAVE                   ),
        .NB_MASTER          ( ariane_soc::NB_PERIPHERALS ),
        .AXI_ADDR_WIDTH     ( AXI_ADDRESS_WIDTH          ),
        .AXI_DATA_WIDTH     ( AXI_DATA_WIDTH             ),
        .AXI_USER_WIDTH     ( AXI_USER_WIDTH             ),
        .AXI_ID_WIDTH       ( AXI_ID_WIDTH               ),
        .MASTER_SLICE_DEPTH ( 2                          ),
        .SLAVE_SLICE_DEPTH  ( 2                          )
    ) i_axi_xbar (
        .clk          ( clk_i      ),
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
    // CLINT
    // ---------------
    logic ipi;
    logic timer_irq;

    clint #(
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_SLAVES ),
        .NR_CORES       ( 1                   )
    ) i_clint (
        .clk_i       ( clk_i                     ),
        .rst_ni      ( ndmreset_n                ),
        .slave       ( master[ariane_soc::CLINT] ),
        .rtc_i       ( rtc_i                     ),
        .timer_irq_o ( timer_irq                 ),
        .ipi_o       ( ipi                       )
    );

    // ---------------
    // Peripherals
    // ---------------
    logic tx, rx;
    logic [1:0] irqs;

    ariane_peripherals #(
      .AxiAddrWidth ( AXI_ADDRESS_WIDTH ),
      .AxiDataWidth ( AXI_DATA_WIDTH    )
    ) i_ariane_peripherals (
      .clk_i     ( clk_i                    ),
      .rst_ni    ( ndmreset_n               ),
      .plic      ( master[ariane_soc::PLIC] ),
      .uart      ( master[ariane_soc::UART] ),
      .spi       ( master[ariane_soc::SPI]  ),
      .irq_o     ( irqs                     ),
      .rx_i      ( rx                       ),
      .tx_o      ( tx                       ),
      .spi_clk_o ( ),
      .spi_mosi  ( ),
      .spi_miso  ( ),
      .spi_ss    ( )
    );

    uart_bus #(.BAUD_RATE(115200), .PARITY_EN(0)) i_uart_bus (.rx(tx), .tx(rx), .rx_en(1'b1));

    // ---------------
    // Core
    // ---------------
    ariane #(
        .CACHE_START_ADDR ( CACHE_START_ADDR ),
        .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH   ( AXI_USER_WIDTH   )
    ) i_ariane (
        .clk_i         ( clk_i            ),
        .rst_ni        ( ndmreset_n       ),
        .boot_addr_i   ( 64'h10000        ), // start fetching from ROM
        .core_id_i     ( '0               ),
        .cluster_id_i  ( '0               ),
        .irq_i         ( irqs             ),
        .ipi_i         ( ipi              ),
        .time_irq_i    ( timer_irq        ),
        .debug_req_i   ( debug_req_core   ),
        .data_if       ( slave[2]         ),
        .bypass_if     ( slave[1]         ),
        .instr_if      ( slave[0]         )
    );

endmodule

