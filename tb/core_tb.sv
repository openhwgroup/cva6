// Author: Florian Zaruba, ETH Zurich
// Date: 15/04/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

import ariane_pkg::*;

module core_tb;

    import uvm_pkg::*;
    import core_lib_pkg::*;

    logic clk_i;
    logic rst_ni;

    mem_if instr_if(clk_i);
    mem_if data_if(clk_i);
    debug_if debug_if();
    core_if core_if(clk_i);


    logic [63:0] instr_if_address;
    logic        instr_if_data_req;
    logic [3:0]  instr_if_data_be;
    logic        instr_if_data_gnt;
    logic        instr_if_data_rvalid;
    logic [31:0] instr_if_data_rdata;

    logic [63:0] data_if_address_i;
    logic [63:0] data_if_data_wdata_i;
    logic        data_if_data_req_i;
    logic        data_if_data_we_i;
    logic [7:0]  data_if_data_be_i;
    logic [1:0]  data_if_tag_status_i;
    logic        data_if_data_gnt_o;
    logic        data_if_data_rvalid_o;
    logic [63:0] data_if_data_rdata_o;

    core_mem core_mem_i (
        .clk_i                   ( clk_i                  ),
        .rst_ni                  ( rst_ni                 ),
        .instr_if_address_i      ( instr_if_address       ),
        .instr_if_data_req_i     ( instr_if_data_req      ),
        .instr_if_data_be_i      ( instr_if_data_be       ),
        .instr_if_data_gnt_o     ( instr_if_data_gnt      ),
        .instr_if_data_rvalid_o  ( instr_if_data_rvalid   ),
        .instr_if_data_rdata_o   ( instr_if_data_rdata    ),
        .data_if_address_i       ( data_if_address_i      ),
        .data_if_data_wdata_i    ( data_if_data_wdata_i   ),
        .data_if_data_req_i      ( data_if_data_req_i     ),
        .data_if_data_we_i       ( data_if_data_we_i      ),
        .data_if_data_be_i       ( data_if_data_be_i      ),
        .data_if_tag_status_i    ( data_if_tag_status_i   ),
        .data_if_data_gnt_o      ( data_if_data_gnt_o     ),
        .data_if_data_rvalid_o   ( data_if_data_rvalid_o  ),
        .data_if_data_rdata_o    ( data_if_data_rdata_o   )
    );

    ariane dut (
        .clk_i                   ( clk_i                ),
        .rst_ni                  ( rst_ni               ),
        .clock_en_i              ( core_if.clock_en     ),
        .test_en_i               ( core_if.test_en      ),
        .fetch_enable_i          ( core_if.fetch_enable ),
        .core_busy_o             ( core_if.core_busy    ),
        .ext_perf_counters_i     (                      ),
        .boot_addr_i             ( core_if.boot_addr    ),
        .core_id_i               ( core_if.core_id      ),
        .cluster_id_i            ( core_if.cluster_id   ),

        .instr_if_address_o      ( instr_if_address     ),
        .instr_if_data_req_o     ( instr_if_data_req    ),
        .instr_if_data_be_o      ( instr_if_data_be     ),
        .instr_if_data_gnt_i     ( instr_if_data_gnt    ),
        .instr_if_data_rvalid_i  ( instr_if_data_rvalid ),
        .instr_if_data_rdata_i   ( instr_if_data_rdata  ),

        .data_if_address_index_o (                      ),
        .data_if_address_tag_o   (                      ),
        .data_if_data_wdata_o    ( data_if.data_wdata   ),
        .data_if_data_req_o      ( data_if.data_req     ),
        .data_if_data_we_o       ( data_if.data_we      ),
        .data_if_data_be_o       ( data_if.data_be      ),
        .data_if_kill_req_o      (                      ),
        .data_if_tag_valid_o     (                      ),
        .data_if_data_gnt_i      ( data_if.data_gnt     ),
        .data_if_data_rvalid_i   ( data_if.data_rvalid  ),
        .data_if_data_rdata_i    ( data_if.data_rdata   ),

        .irq_i                   ( core_if.irq          ),
        .irq_id_i                ( core_if.irq_id       ),
        .irq_ack_o               ( core_if.irq_ack      ),
        .irq_sec_i               ( core_if.irq_sec      ),
        .sec_lvl_o               ( core_if.sec_lvl      ),

        .debug_req_i             (                      ),
        .debug_gnt_o             (                      ),
        .debug_rvalid_o          (                      ),
        .debug_addr_i            (                      ),
        .debug_we_i              (                      ),
        .debug_wdata_i           (                      ),
        .debug_rdata_o           (                      ),
        .debug_halted_o          (                      ),
        .debug_halt_i            (                      ),
        .debug_resume_i          (                      )
    );

    // clock process
    initial begin
        clk_i = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #10ns clk_i = ~clk_i;
        rst_ni = 1'b1;
        forever
            #10ns clk_i = ~clk_i;
    end

    task preload_memories();
        logic [7:0] rmem [0:1024];

        $display("Reading memory");
        $readmemh("test/add_test.v", rmem, 0);

        // copy bitwise from verilog file
        for (int i = 0; i < 1024/8; i++) begin
            for (int j = 0; j < 8; j++)
                core_mem_i.ram_i.mem[i][j] = rmem[i*8 + j];
        end

    endtask : preload_memories

    program testbench (core_if core_if, mem_if instr_if);
        initial begin
            uvm_config_db #(virtual core_if)::set(null, "uvm_test_top", "core_if", core_if);
            uvm_config_db #(virtual mem_if )::set(null, "uvm_test_top", "instr_mem_if", instr_if);
            // print the topology
            uvm_top.enable_print_topology = 1;
            // Start UVM test
            run_test();
        end

        initial begin
            preload_memories();
        end
    endprogram

    testbench tb(core_if, instr_if);
endmodule