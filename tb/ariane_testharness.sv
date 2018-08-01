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
        parameter int unsigned AXI_ID_WIDTH      = 10,
        parameter int unsigned AXI_USER_WIDTH    = 1,
        parameter int unsigned AXI_ADDRESS_WIDTH = 64,
        parameter int unsigned AXI_DATA_WIDTH    = 64,
        parameter int unsigned NUM_WORDS         = 2**24          // memory size
    )(
        input  logic                           clk_i,
        input  logic                           rst_ni,
        output logic [31:0]                    exit_o
    );

    // disable test-enable
    logic        test_en;
    logic        ndmreset;
    logic        ndmreset_n;
    logic        debug_req;

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
    logic [6:0]  debug_req_bits_addr;
    logic [1:0]  debug_req_bits_op;
    logic [31:0] debug_req_bits_data;
    logic        debug_resp_valid;
    logic        debug_resp_ready;
    logic [1:0]  debug_resp_bits_resp;
    logic [31:0] debug_resp_bits_data;

    logic        jtag_req_valid;
    logic [6:0]  jtag_req_bits_addr;
    logic [1:0]  jtag_req_bits_op;
    logic [31:0] jtag_req_bits_data;
    logic        jtag_resp_ready;
    logic        jtag_resp_valid;

    logic        dmi_req_valid;
    logic [6:0]  dmi_req_bits_addr;
    logic [1:0]  dmi_req_bits_op;
    logic [31:0] dmi_req_bits_data;
    logic        dmi_resp_ready;
    logic        dmi_resp_valid;

    assign test_en = 1'b0;
    assign ndmreset_n = ~ndmreset ;

    localparam NB_SLAVE = 3;
    localparam NB_MASTER = 3;
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
    ) master[NB_MASTER-1:0]();

    // ---------------
    // Debug
    // ---------------
    assign init_done = rst_ni;

    initial begin
        if (!$value$plusargs("jtag_rbb_enable=%b", jtag_enable)) jtag_enable = 'h0;
    end

    // debug if MUX
    assign debug_req_valid     = (jtag_enable[0]) ? jtag_req_valid     : dmi_req_valid;
    assign debug_req_bits_addr = (jtag_enable[0]) ? jtag_req_bits_addr : dmi_req_bits_addr;
    assign debug_req_bits_op   = (jtag_enable[0]) ? jtag_req_bits_op   : dmi_req_bits_op;
    assign debug_req_bits_data = (jtag_enable[0]) ? jtag_req_bits_data : dmi_req_bits_data;
    assign debug_resp_ready    = (jtag_enable[0]) ? jtag_resp_ready    : dmi_resp_ready;
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
        .clk_i                ( clk_i                ),
        .rst_ni               ( rst_ni               ),

        .dmi_rst_no           (                      ),
        .dmi_req_valid_o      ( jtag_req_valid       ),
        .dmi_req_ready_i      ( debug_req_ready      ),
        .dmi_req_bits_addr_o  ( jtag_req_bits_addr   ),
        .dmi_req_bits_op_o    ( jtag_req_bits_op     ),
        .dmi_req_bits_data_o  ( jtag_req_bits_data   ),
        .dmi_resp_valid_i     ( jtag_resp_valid      ),
        .dmi_resp_ready_o     ( jtag_resp_ready      ),
        .dmi_resp_bits_resp_i ( debug_resp_bits_resp ),
        .dmi_resp_bits_data_i ( debug_resp_bits_data ),

        .tck_i                ( jtag_TCK             ),
        .tms_i                ( jtag_TMS             ),
        .trst_ni              ( jtag_TRSTn           ),
        .td_i                 ( jtag_TDI             ),
        .td_o                 ( jtag_TDO_data        ),
        .tdo_oe_o             ( jtag_TDO_driven      )
    );

    // SiFive's SimDTM Module
    // Converts to DPI calls
    SimDTM i_SimDTM (
        .clk                  ( clk_i                ),
        .reset                ( ~rst_ni              ),
        .debug_req_valid      ( dmi_req_valid        ),
        .debug_req_ready      ( debug_req_ready      ),
        .debug_req_bits_addr  ( dmi_req_bits_addr    ),
        .debug_req_bits_op    ( dmi_req_bits_op      ),
        .debug_req_bits_data  ( dmi_req_bits_data    ),
        .debug_resp_valid     ( dmi_resp_valid       ),
        .debug_resp_ready     ( dmi_resp_ready       ),
        .debug_resp_bits_resp ( debug_resp_bits_resp ),
        .debug_resp_bits_data ( debug_resp_bits_data ),
        .exit                 ( dmi_exit             )
    );

    // debug module
    dm_top #(
        // current implementation only supports 1 hart
        .NrHarts              ( 1                    ),
        .AxiIdWidth           ( AXI_ID_WIDTH_SLAVES  ),
        .AxiAddrWidth         ( AXI_ADDRESS_WIDTH    ),
        .AxiDataWidth         ( AXI_DATA_WIDTH       ),
        .AxiUserWidth         ( AXI_USER_WIDTH       )
    ) i_dm_top (
        .clk_i                ( clk_i                ),
        .rst_ni               ( rst_ni               ), // PoR
        .ndmreset_o           ( ndmreset             ),
        .dmactive_o           (                      ), // active debug session
        .debug_req_o          ( debug_req            ),
        .axi_slave            ( master[2]            ),
        .dmi_rst_ni           ( rst_ni               ),
        .dmi_req_valid_i      ( debug_req_valid      ),
        .dmi_req_ready_o      ( debug_req_ready      ),
        .dmi_req_bits_addr_i  ( debug_req_bits_addr  ),
        .dmi_req_bits_op_i    ( debug_req_bits_op    ),
        .dmi_req_bits_data_i  ( debug_req_bits_data  ),
        .dmi_resp_valid_o     ( debug_resp_valid     ),
        .dmi_resp_ready_i     ( debug_resp_ready     ),
        .dmi_resp_bits_resp_o ( debug_resp_bits_resp ),
        .dmi_resp_bits_data_o ( debug_resp_bits_data )
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
        .clk_i  ( clk_i      ),
        .rst_ni ( ndmreset_n ),
        .slave  ( master[1]  ),
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

    // ---------------
    // Memory
    // ---------------
    logic                         req;
    logic                         we;
    logic [AXI_ADDRESS_WIDTH-1:0] addr;
    logic [AXI_DATA_WIDTH/8-1:0]  be;
    logic [AXI_DATA_WIDTH-1:0]    wdata;
    logic [AXI_DATA_WIDTH-1:0]    rdata;
    logic [AXI_DATA_WIDTH-1:0]    bit_en;

    // convert byte enable to bit enable
    for (genvar i = 0; i < AXI_DATA_WIDTH/8; i++) begin
        assign bit_en[i*8 +: 8] = {8{be[i]}};
    end

    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH_SLAVES ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH      )
    ) i_axi2mem (
        .clk_i  ( clk_i      ),
        .rst_ni ( ndmreset_n ),
        .slave  ( master[0]  ),
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
        .req_i      ( req                                                                         ),
        .we_i       ( we                                                                          ),
        .addr_i     ( addr[$clog2(NUM_WORDS)-1+$clog2(AXI_DATA_WIDTH/8):$clog2(AXI_DATA_WIDTH/8)] ),
        .wdata_i    ( wdata                                                                       ),
        .be_i       ( bit_en                                                                      ),
        .rdata_o    ( rdata                                                                       )
    );

    // ---------------
    // AXI Xbar
    // ---------------
    axi_node_intf_wrap #(
        // three ports from Ariane (instruction, data and bypass)
        .NB_SLAVE       ( NB_SLAVE          ),
        .NB_MASTER      ( NB_MASTER         ), // debug unit, memory unit
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      )
    ) i_axi_xbar (
        .clk          ( clk_i                                          ),
        .rst_n        ( ndmreset_n                                     ),
        .test_en_i    ( test_en                                        ),
        .slave        ( slave                                          ),
        .master       ( master                                         ),
        .start_addr_i ( {64'h0,   64'h10000, CACHE_START_ADDR}         ),
        .end_addr_i   ( {64'hFFF, 64'h1FFFF, CACHE_START_ADDR + 2**24} )
    );

    // ---------------
    // Core
    // ---------------
    ariane #(
        .CACHE_START_ADDR ( CACHE_START_ADDR ),
        .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH   ( AXI_USER_WIDTH   )
    ) i_ariane (
        .clk_i                ( clk_i            ),
        .rst_ni               ( ndmreset_n       ),
        .test_en_i            ( test_en          ),
        .boot_addr_i          ( 64'h10000        ), // start fetching from ROM
        .core_id_i            ( '0               ),
        .cluster_id_i         ( '0               ),
        .irq_i                ( '0               ),
        .ipi_i                ( '0               ),
        .time_irq_i           ( '0               ),
        .debug_req_i          ( debug_req        ),
        .data_if              ( slave[2]         ),
        .bypass_if            ( slave[1]         ),
        .instr_if             ( slave[0]         )
    );

endmodule

