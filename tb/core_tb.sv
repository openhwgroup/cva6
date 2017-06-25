// Author: Florian Zaruba, ETH Zurich
// Date: 15/04/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//

import ariane_pkg::*;
import uvm_pkg::*;
import core_lib_pkg::*;

`define DRAM_BASE 64'h80000000


module core_tb;
    import "DPI-C" function chandle read_elf(string fn);
    import "DPI-C" function longint unsigned get_symbol_address(string symb);
    import "DPI-C" function longint unsigned get_symbol_size(string symb);

    logic clk_i;
    logic rst_ni;
    logic rtc_i;

    debug_if debug_if();
    core_if core_if (clk_i);
    dcache_if dcache_if (clk_i);

    logic [63:0] instr_if_address;
    logic        instr_if_data_req;
    logic [3:0]  instr_if_data_be;
    logic        instr_if_data_gnt;
    logic        instr_if_data_rvalid;
    logic [31:0] instr_if_data_rdata;

    logic [11:0] data_if_address_index_i;
    logic [43:0] data_if_address_tag_i;
    logic [63:0] data_if_data_wdata_i;
    logic        data_if_data_req_i;
    logic        data_if_data_we_i;
    logic [7:0]  data_if_data_be_i;
    logic        data_if_kill_req_i;
    logic        data_if_tag_valid_i;
    logic        data_if_data_gnt_o;
    logic        data_if_data_rvalid_o;
    logic [63:0] data_if_data_rdata_o;

    // connect D$ interface
    assign dcache_if.address_index = data_if_address_index_i;
    assign dcache_if.address_tag   = data_if_address_tag_i;
    assign dcache_if.data_wdata    = data_if_data_wdata_i;
    assign dcache_if.data_req      = data_if_data_req_i;
    assign dcache_if.data_we       = data_if_data_we_i;
    assign dcache_if.data_be       = data_if_data_be_i;
    assign dcache_if.kill_req      = data_if_kill_req_i;
    assign dcache_if.tag_valid     = data_if_tag_valid_i;
    assign dcache_if.data_gnt      = data_if_data_gnt_o;
    assign dcache_if.data_rvalid   = data_if_data_rvalid_o;
    assign dcache_if.data_rdata    = data_if_data_rdata_o;

    core_mem core_mem_i (
        .clk_i                   ( clk_i                   ),
        .rst_ni                  ( rst_ni                  ),
        .instr_if_address_i      ( instr_if_address        ),
        .instr_if_data_req_i     ( instr_if_data_req       ),
        .instr_if_data_be_i      ( instr_if_data_be        ),
        .instr_if_data_gnt_o     ( instr_if_data_gnt       ),
        .instr_if_data_rvalid_o  ( instr_if_data_rvalid    ),
        .instr_if_data_rdata_o   ( instr_if_data_rdata     ),

        .data_if_address_index_i ( data_if_address_index_i ),
        .data_if_address_tag_i   ( data_if_address_tag_i   ),
        .data_if_data_wdata_i    ( data_if_data_wdata_i    ),
        .data_if_data_req_i      ( data_if_data_req_i      ),
        .data_if_data_we_i       ( data_if_data_we_i       ),
        .data_if_data_be_i       ( data_if_data_be_i       ),
        .data_if_kill_req_i      ( data_if_kill_req_i      ),
        .data_if_tag_valid_i     ( data_if_tag_valid_i     ),
        .data_if_data_gnt_o      ( data_if_data_gnt_o      ),
        .data_if_data_rvalid_o   ( data_if_data_rvalid_o   ),
        .data_if_data_rdata_o    ( data_if_data_rdata_o    )
    );

    ariane dut (
        .clk_i                   ( clk_i                    ),
        .rst_ni                  ( rst_ni                   ),
        .rtc_i                   ( rtc_i                    ),
        .clock_en_i              ( core_if.clock_en         ),
        .test_en_i               ( core_if.test_en          ),
        .fetch_enable_i          ( core_if.fetch_enable     ),
        .core_busy_o             ( core_if.core_busy        ),
        .ext_perf_counters_i     (                          ),
        .boot_addr_i             ( core_if.boot_addr        ),
        .core_id_i               ( core_if.core_id          ),
        .cluster_id_i            ( core_if.cluster_id       ),

        .instr_if_address_o      ( instr_if_address         ),
        .instr_if_data_req_o     ( instr_if_data_req        ),
        .instr_if_data_be_o      ( instr_if_data_be         ),
        .instr_if_data_gnt_i     ( instr_if_data_gnt        ),
        .instr_if_data_rvalid_i  ( instr_if_data_rvalid     ),
        .instr_if_data_rdata_i   ( instr_if_data_rdata      ),

        .data_if_address_index_o ( data_if_address_index_i  ),
        .data_if_address_tag_o   ( data_if_address_tag_i    ),
        .data_if_data_wdata_o    ( data_if_data_wdata_i     ),
        .data_if_data_req_o      ( data_if_data_req_i       ),
        .data_if_data_we_o       ( data_if_data_we_i        ),
        .data_if_data_be_o       ( data_if_data_be_i        ),
        .data_if_kill_req_o      ( data_if_kill_req_i       ),
        .data_if_tag_valid_o     ( data_if_tag_valid_i      ),
        .data_if_data_gnt_i      ( data_if_data_gnt_o       ),
        .data_if_data_rvalid_i   ( data_if_data_rvalid_o    ),
        .data_if_data_rdata_i    ( data_if_data_rdata_o     ),

        .irq_i                   ( {core_if.irq, core_if.irq}              ),
        .irq_id_i                ( core_if.irq_id           ),
        .irq_ack_o               ( core_if.irq_ack          ),
        .irq_sec_i               ( core_if.irq_sec          ),
        .sec_lvl_o               ( core_if.sec_lvl          ),

        .debug_req_i             (                          ),
        .debug_gnt_o             (                          ),
        .debug_rvalid_o          (                          ),
        .debug_addr_i            (                          ),
        .debug_we_i              (                          ),
        .debug_wdata_i           (                          ),
        .debug_rdata_o           (                          ),
        .debug_halted_o          (                          ),
        .debug_halt_i            (                          ),
        .debug_resume_i          (                          )
    );

    // Clock process
    initial begin
        clk_i = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #10ns clk_i = ~clk_i;
        rst_ni = 1'b1;
        forever
            #10ns clk_i = ~clk_i;
    end
    // Real Time Clock
    initial begin
        rtc_i = 1'b0;
        forever
            #15.258us rtc_i = ~rtc_i;
    end

    task preload_memories();
        static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();
        string plus_args [$];

        longint unsigned address;
        longint unsigned bss_address;
        longint unsigned bss_size;

        string file;
        string test;
        // offset the temporary RAM
        logic [7:0] rmem [`DRAM_BASE:`DRAM_BASE + 16384];
        // get the file name from a command line plus arg
        void'(uvcl.get_arg_value("+ASMTEST=",file));

        $display("Pre-loading memory from file: %s\n", file);
        // read elf file (DPI call)
        void'(read_elf(file));
        // we are interested in the .tohost ELF symbol in-order to observe end of test signals
        address = get_symbol_address(".tohost");
        // get the objdump verilog file to load our memorys
        $readmemh({file, ".v"}, rmem);
        // copy bitwise from verilog file
        for (int i = 0; i < 16384/8; i++) begin
            for (int j = 0; j < 8; j++)
                core_mem_i.ram_i.mem[i][j] = rmem[`DRAM_BASE + i*8 + j];
        end
        // initialize .bss
        bss_address = get_symbol_address(".bss");
        bss_size    = get_symbol_size(".bss");
        // `uvm_info("Core Test",  $sformatf(".bss address: %x, .bss size: %x, .tohost address: %x", ((bss_address - `DRAM_BASE) >> 3), bss_size, address), UVM_LOW)

        // the section should be aligned on a double word boundary
        for (int i = 0; i < bss_size/8; i++) begin
                core_mem_i.ram_i.mem[((bss_address - `DRAM_BASE) >> 3) + i] = 64'b0;
        end
        // pass tohost address to UVM resource DB
        uvm_config_db #(longint unsigned)::set(null, "uvm_test_top.m_env.m_eoc", "tohost", address);

    endtask : preload_memories

    program testbench (core_if core_if, dcache_if dcache_if);
        initial begin
            uvm_config_db #(virtual core_if)::set(null, "uvm_test_top", "core_if", core_if);
            uvm_config_db #(virtual dcache_if )::set(null, "uvm_test_top", "dcache_if", dcache_if);
            // print the topology
            // uvm_top.enable_print_topology = 1;
            // Start UVM test
            run_test();
        end

        initial begin
            preload_memories();
        end
    endprogram

    testbench tb(core_if, dcache_if);
endmodule