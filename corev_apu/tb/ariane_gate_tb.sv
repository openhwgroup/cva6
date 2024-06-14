// Copyright 2024 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Guillaume Chauvon - Thales
//

import uvm_pkg::*;

`include "axi/assign.svh"
`include "rvfi_types.svh"

`ifdef VERILATOR
`include "custom_uvm_macros.svh"
`else
`include "uvm_macros.svh"
`endif

`define MAIN_MEM(P) i_sram.gen_cut[0].i_tc_sram_wrapper.i_tc_sram.init_val[(``P``)]
`define USER_MEM(P) i_sram.gen_cut[0].gen_mem_user.i_tc_sram_wrapper_user.i_tc_sram.init_val[(``P``)]

`timescale 1ns/1ns

import "DPI-C" function void read_elf(input string filename);
import "DPI-C" function byte get_section(output longint address, output longint len);
import "DPI-C" context function void read_section_sv(input longint address, inout byte buffer[]);
import "DPI-C" function string getenv(input string env_name);

module ariane_gate_tb;

    // cva6 configuration
    localparam config_pkg::cva6_cfg_t CVA6Cfg = build_config_pkg::build_config(cva6_config_pkg::cva6_cfg);
    static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();

    localparam int unsigned AXI_USER_WIDTH    = CVA6Cfg.AxiUserWidth;
    localparam int unsigned AXI_USER_EN       = CVA6Cfg.AXI_USER_EN;
    localparam int unsigned AXI_ADDRESS_WIDTH = 64;
    localparam int unsigned AXI_DATA_WIDTH    = 64;


    localparam NrSlaves = 1;
    localparam NB_PERIPHERALS = 3;
    localparam IdWidthSlave = ariane_axi_soc::IdWidth + $clog2(NrSlaves);

    localparam NUM_WORDS = 2**16;
    int unsigned CLOCK_PERIOD = 20ns;
    logic clk_i;
    logic rst_ni;

    longint unsigned cycles;
    longint unsigned max_cycles;

    logic [31:0] exit_o;
    localparam [7:0] hart_id = '0;

    // RVFI
    localparam type rvfi_instr_t = `RVFI_INSTR_T(CVA6Cfg);
    localparam type rvfi_csr_elmt_t = `RVFI_CSR_ELMT_T(CVA6Cfg);
    localparam type rvfi_csr_t = `RVFI_CSR_T(CVA6Cfg, rvfi_csr_elmt_t);

    // RVFI PROBES
    localparam type rvfi_probes_instr_t = `RVFI_PROBES_INSTR_T(CVA6Cfg);
    localparam type rvfi_probes_csr_t = `RVFI_PROBES_CSR_T(CVA6Cfg);
    localparam type rvfi_probes_t = struct packed {
      logic csr;
      rvfi_probes_instr_t instr;
    };

    string binary = "";


    typedef enum int unsigned {
        DRAM     = 0,
        UART     = 1,
        ROM      = 2
    } axi_slaves_t;

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
        .AXI_ID_WIDTH   ( ariane_axi_soc::IdWidth ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH      )
    ) slave[NrSlaves-1:0]();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
        .AXI_ID_WIDTH   ( IdWidthSlave ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
    ) master[NB_PERIPHERALS-1:0]();

    // ---------------
    // Core
    // ---------------
    ariane_axi::req_t    axi_ariane_req;
    ariane_axi::resp_t   axi_ariane_resp;
    rvfi_probes_t rvfi_probes;
    rvfi_csr_t rvfi_csr;
    rvfi_instr_t [CVA6Cfg.NrCommitPorts-1:0]  rvfi_instr;

    ariane #(
        .CVA6Cfg              ( CVA6Cfg             ),
        .rvfi_probes_instr_t  ( rvfi_probes_instr_t ),
        .rvfi_probes_csr_t    ( rvfi_probes_csr_t   ),
        .rvfi_probes_t        ( rvfi_probes_t       ),
        .noc_req_t            ( ariane_axi::req_t   ),
        .noc_resp_t           ( ariane_axi::resp_t  )
    ) i_ariane (
        .clk_i                ( clk_i               ),
        .rst_ni               ( rst_ni              ),
        .boot_addr_i          ( ariane_soc::ROMBase), // start fetching from ROM
        .hart_id_i            ( {56'h0, hart_id}    ),
        .irq_i                ( 2'b00 /*irqs*/      ),
        .ipi_i                ( 1'b0  /*ipi*/       ),
        .time_irq_i           ( 1'b0  /*timer_irq*/ ),
        .debug_req_i          ( 1'b0                ),
        .rvfi_probes_o        ( rvfi_probes         ),
        .noc_req_o            ( axi_ariane_req      ),
        .noc_resp_i           ( axi_ariane_resp     )
    );

    `AXI_ASSIGN_FROM_REQ(slave[0], axi_ariane_req)
    `AXI_ASSIGN_TO_RESP(axi_ariane_resp, slave[0])
  // -------------
  // Simulation Helper Functions
  // -------------
  // check for response errors
    always_ff @(posedge clk_i) begin : p_assert
        if (axi_ariane_req.r_ready &&
            axi_ariane_resp.r_valid &&
            axi_ariane_resp.r.resp inside {axi_pkg::RESP_DECERR, axi_pkg::RESP_SLVERR}) begin
            $warning("R Response Errored");
        end
        if (axi_ariane_req.b_ready &&
            axi_ariane_resp.b_valid &&
            axi_ariane_resp.b.resp inside {axi_pkg::RESP_DECERR, axi_pkg::RESP_SLVERR}) begin
            $warning("B Response Errored");
        end
    end

    cva6_rvfi #(
      .CVA6Cfg   (CVA6Cfg),
      .rvfi_instr_t(rvfi_instr_t),
      .rvfi_csr_t(rvfi_csr_t),
      .rvfi_probes_instr_t(rvfi_probes_instr_t),
      .rvfi_probes_csr_t(rvfi_probes_csr_t),
      .rvfi_probes_t(rvfi_probes_t)
  ) i_cva6_rvfi (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .rvfi_probes_i(rvfi_probes),
      .rvfi_instr_o(rvfi_instr),
      .rvfi_csr_o(rvfi_csr)
  );

  rvfi_tracer  #(
    .CVA6Cfg(CVA6Cfg),
    .rvfi_instr_t(rvfi_instr_t),
    .rvfi_csr_t(rvfi_csr_t),
    //
    .HART_ID(hart_id),
    .DEBUG_START(0),
    .DEBUG_STOP(0)
  ) i_rvfi_tracer (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rvfi_i(rvfi_instr),
    .rvfi_csr_i(rvfi_csr),
    .end_of_test_o(rvfi_exit)
  );

    assign exit_o = rvfi_exit;


    // ------------------------------
    // Memory + Exclusive Access
    // ------------------------------

    logic                         req;
    logic                         we;
    logic [AXI_ADDRESS_WIDTH-1:0] addr;
    logic [AXI_DATA_WIDTH/8-1:0]  be;
    logic [AXI_DATA_WIDTH-1:0]    wdata;
    logic [AXI_DATA_WIDTH-1:0]    rdata;
    logic [AXI_USER_WIDTH-1:0]    wuser;
    logic [AXI_USER_WIDTH-1:0]    ruser;

    axi2mem #(
        .AXI_ID_WIDTH   ( IdWidthSlave ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
    ) i_axi2mem (
        .clk_i  ( clk_i        ),
        .rst_ni ( rst_ni       ),
        .slave  ( master[DRAM] ), // dram_delayed ?
        .req_o  ( req          ),
        .we_o   ( we           ),
        .addr_o ( addr         ),
        .be_o   ( be           ),
        .user_o ( wuser        ),
        .data_o ( wdata        ),
        .user_i ( ruser        ),
        .data_i ( rdata        )
    );

    sram #(
        .DATA_WIDTH ( AXI_DATA_WIDTH ),
        .USER_WIDTH ( AXI_USER_WIDTH ),
        .USER_EN    ( AXI_USER_EN    ),
    `ifdef VERILATOR
        .SIM_INIT   ( "none"         ),
    `else
        .SIM_INIT   ( "zeros"        ),
    `endif
        .NUM_WORDS  ( NUM_WORDS      )
    ) i_sram (
        .clk_i      ( clk_i                                                                       ),
        .rst_ni     ( rst_ni                                                                      ),
        .req_i      ( req                                                                         ),
        .we_i       ( we                                                                          ),
        .addr_i     ( addr[$clog2(NUM_WORDS)-1+$clog2(AXI_DATA_WIDTH/8):$clog2(AXI_DATA_WIDTH/8)] ),
        .wuser_i    ( wuser                                                                       ),
        .wdata_i    ( wdata                                                                       ),
        .be_i       ( be                                                                          ),
        .ruser_o    ( ruser                                                                       ),
        .rdata_o    ( rdata                                                                       )
    );

    // ---------------
    // ROM
    // ---------------
    logic                         rom_req;
    logic [AXI_ADDRESS_WIDTH-1:0] rom_addr;
    logic [AXI_DATA_WIDTH-1:0]    rom_rdata;

    axi2mem #(
        .AXI_ID_WIDTH   ( IdWidthSlave ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
    ) i_axi2rom (
        .clk_i  ( clk_i                   ),
        .rst_ni ( rst_ni                  ),
        .slave  ( master[ROM]             ),
        .req_o  ( rom_req                 ),
        .we_o   (                         ),
        .addr_o ( rom_addr                ),
        .be_o   (                         ),
        .user_o (                         ),
        .data_o (                         ),
        .user_i ( '0                      ),
        .data_i ( rom_rdata               )
    );

    bootrom i_bootrom (
        .clk_i      ( clk_i     ),
        .req_i      ( rom_req   ),
        .addr_i     ( rom_addr  ),
        .rdata_o    ( rom_rdata )
    );

    // ---------------
    // AXI Xbar
    // ---------------

    axi_pkg::xbar_rule_64_t [NB_PERIPHERALS-1:0] addr_map;

    assign addr_map = '{
        '{ idx: ROM,      start_addr: ariane_soc::ROMBase,      end_addr: ariane_soc::ROMBase + ariane_soc::ROMLength           },
        '{ idx: UART,     start_addr: ariane_soc::UARTBase,     end_addr: ariane_soc::UARTBase + ariane_soc::UARTLength         },
        '{ idx: DRAM,     start_addr: ariane_soc::DRAMBase,     end_addr: ariane_soc::DRAMBase + ariane_soc::DRAMLength         }
    };

    localparam axi_pkg::xbar_cfg_t AXI_XBAR_CFG = '{
        NoSlvPorts: unsigned'(NrSlaves),
        NoMstPorts: unsigned'(NB_PERIPHERALS),
        MaxMstTrans: unsigned'(1), // Probably requires update
        MaxSlvTrans: unsigned'(1), // Probably requires update
        FallThrough: 1'b0,
        LatencyMode: axi_pkg::NO_LATENCY,
        AxiIdWidthSlvPorts: unsigned'(ariane_axi_soc::IdWidth),
        AxiIdUsedSlvPorts: unsigned'(ariane_axi_soc::IdWidth),
        UniqueIds: 1'b0,
        AxiAddrWidth: unsigned'(AXI_ADDRESS_WIDTH),
        AxiDataWidth: unsigned'(AXI_DATA_WIDTH),
        NoAddrRules: unsigned'(NB_PERIPHERALS)
    };

    axi_xbar_intf #(
        .AXI_USER_WIDTH ( AXI_USER_WIDTH          ),
        .Cfg            ( AXI_XBAR_CFG            ),
        .rule_t         ( axi_pkg::xbar_rule_64_t )
    ) i_axi_xbar (
        .clk_i                 ( clk_i      ),
        .rst_ni                ( rst_ni     ),
        .test_i                ( '0         ),
        .slv_ports             ( slave      ),
        .mst_ports             ( master     ),
        .addr_map_i            ( addr_map   ),
        .en_default_mst_port_i ( '0         ),
        .default_mst_port_i    ( '0         )
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
        .AXI4_ADDRESS_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI4_RDATA_WIDTH   ( AXI_DATA_WIDTH ),
        .AXI4_WDATA_WIDTH   ( AXI_DATA_WIDTH ),
        .AXI4_ID_WIDTH      ( IdWidthSlave   ),
        .AXI4_USER_WIDTH    ( AXI_USER_WIDTH ),
        .BUFF_DEPTH_SLAVE   ( 2            ),
        .APB_ADDR_WIDTH     ( 32           )
    ) i_axi2apb_64_32_uart (
        .ACLK      ( clk_i          ),
        .ARESETn   ( rst_ni         ),
        .test_en_i ( 1'b0           ),
        .AWID_i    ( master[UART].aw_id     ),
        .AWADDR_i  ( master[UART].aw_addr   ),
        .AWLEN_i   ( master[UART].aw_len    ),
        .AWSIZE_i  ( master[UART].aw_size   ),
        .AWBURST_i ( master[UART].aw_burst  ),
        .AWLOCK_i  ( master[UART].aw_lock   ),
        .AWCACHE_i ( master[UART].aw_cache  ),
        .AWPROT_i  ( master[UART].aw_prot   ),
        .AWREGION_i( master[UART].aw_region ),
        .AWUSER_i  ( master[UART].aw_user   ),
        .AWQOS_i   ( master[UART].aw_qos    ),
        .AWVALID_i ( master[UART].aw_valid  ),
        .AWREADY_o ( master[UART].aw_ready  ),
        .WDATA_i   ( master[UART].w_data    ),
        .WSTRB_i   ( master[UART].w_strb    ),
        .WLAST_i   ( master[UART].w_last    ),
        .WUSER_i   ( master[UART].w_user    ),
        .WVALID_i  ( master[UART].w_valid   ),
        .WREADY_o  ( master[UART].w_ready   ),
        .BID_o     ( master[UART].b_id      ),
        .BRESP_o   ( master[UART].b_resp    ),
        .BVALID_o  ( master[UART].b_valid   ),
        .BUSER_o   ( master[UART].b_user    ),
        .BREADY_i  ( master[UART].b_ready   ),
        .ARID_i    ( master[UART].ar_id     ),
        .ARADDR_i  ( master[UART].ar_addr   ),
        .ARLEN_i   ( master[UART].ar_len    ),
        .ARSIZE_i  ( master[UART].ar_size   ),
        .ARBURST_i ( master[UART].ar_burst  ),
        .ARLOCK_i  ( master[UART].ar_lock   ),
        .ARCACHE_i ( master[UART].ar_cache  ),
        .ARPROT_i  ( master[UART].ar_prot   ),
        .ARREGION_i( master[UART].ar_region ),
        .ARUSER_i  ( master[UART].ar_user   ),
        .ARQOS_i   ( master[UART].ar_qos    ),
        .ARVALID_i ( master[UART].ar_valid  ),
        .ARREADY_o ( master[UART].ar_ready  ),
        .RID_o     ( master[UART].r_id      ),
        .RDATA_o   ( master[UART].r_data    ),
        .RRESP_o   ( master[UART].r_resp    ),
        .RLAST_o   ( master[UART].r_last    ),
        .RUSER_o   ( master[UART].r_user    ),
        .RVALID_o  ( master[UART].r_valid   ),
        .RREADY_i  ( master[UART].r_ready   ),
        .PENABLE   ( uart_penable   ),
        .PWRITE    ( uart_pwrite    ),
        .PADDR     ( uart_paddr     ),
        .PSEL      ( uart_psel      ),
        .PWDATA    ( uart_pwdata    ),
        .PRDATA    ( uart_prdata    ),
        .PREADY    ( uart_pready    ),
        .PSLVERR   ( uart_pslverr   )
    );

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




    // Clock process
    initial begin
    
        string SIMU_PERIOD = {getenv("SIMU_PERIOD"),"ns"};
        if (SIMU_PERIOD != "ns")
			CLOCK_PERIOD = SIMU_PERIOD.atoi();
		
        clk_i = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #(CLOCK_PERIOD/2) clk_i = ~clk_i;
        rst_ni = 1'b1;
        forever begin
            #(CLOCK_PERIOD/2) clk_i = 1'b1;
            #(CLOCK_PERIOD/2) clk_i = 1'b0;

            //if (cycles > max_cycles)
            //    $fatal(1, "Simulation reached maximum cycle count of %d", max_cycles);

            cycles++;
        end
    end


    initial begin
        forever begin

            wait (exit_o[0]);

            if ((exit_o >> 1)) begin
                `uvm_error( "Core Test",  $sformatf("*** FAILED *** (tohost = %0d)", (exit_o >> 1)))
            end else begin
                `uvm_info( "Core Test",  $sformatf("*** SUCCESS *** (tohost = %0d)", (exit_o >> 1)), UVM_LOW)
            end

            $finish();
        end
    end

    // for faster simulation we can directly preload the ELF
    // Note that we are loosing the capabilities to use risc-fesvr though
    initial begin
        automatic logic [7:0][7:0] mem_row;
        longint address, len;
        byte buffer[];
        void'(uvcl.get_arg_value("+elf_file=", binary));

        if (binary != "") begin
            `uvm_info( "Core Test", $sformatf("Preloading ELF: %s", binary), UVM_LOW)

            void'(read_elf(binary));
            // wait with preloading, otherwise randomization will overwrite the existing value
            wait(clk_i);

            // while there are more sections to process
            while (get_section(address, len)) begin
                automatic int num_words = (len+7)/8;
                `uvm_info( "Core Test", $sformatf("Loading Address: %x, Length: %x", address, len),UVM_LOW)
                buffer = new [num_words*8];
                void'(read_section_sv(address, buffer));
                // preload memories
                // 64-bit
                for (int i = 0; i < num_words; i++) begin
                    mem_row = '0;
                    for (int j = 0; j < 8; j++) begin
                        mem_row[j] = buffer[i*8 + j];
                    end
                    if (address[31:0] < 'h84000000) begin
                    `MAIN_MEM((address[23:0] >> 3) + i) = mem_row;
                    end else begin
                    `USER_MEM((address[23:0] >> 3) + i) = mem_row;
                    end
                end
            end
        end
    end
endmodule
