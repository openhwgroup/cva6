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

    mem_if #(.DATA_WIDTH(32)) instr_if(clk_i);
    mem_if data_if(clk_i);
    debug_if debug_if();
    core_if core_if(clk_i);

    ariane dut (
        .clk_i                  ( clk_i                ),
        .rst_ni                 ( rst_ni               ),
        .clock_en_i             ( core_if.clock_en     ),
        .test_en_i              ( core_if.test_en      ),
        .fetch_enable_i         ( core_if.fetch_enable ),
        .core_busy_o            ( core_if.core_busy    ),
        .ext_perf_counters_i    (                      ),
        .boot_addr_i            ( core_if.boot_addr    ),
        .core_id_i              ( core_if.core_id      ),
        .cluster_id_i           ( core_if.cluster_id   ),

        .instr_if_address_o     ( instr_if.address     ),
        .instr_if_data_req_o    ( instr_if.data_req & instr_if.data_req   ),
        .instr_if_data_be_o     ( instr_if.data_be     ),
        .instr_if_data_gnt_i    ( instr_if.data_gnt    ),
        .instr_if_data_rvalid_i ( instr_if.data_rvalid ),
        .instr_if_data_rdata_i  ( instr_if.data_rdata  ),

        .data_if_address_o      ( data_if.address      ),
        .data_if_data_wdata_o   ( data_if.data_wdata   ),
        .data_if_data_req_o     ( data_if.data_req     ),
        .data_if_data_we_o      ( data_if.data_we      ),
        .data_if_data_be_o      ( data_if.data_be      ),
        .data_if_data_gnt_i     ( data_if.data_gnt     ),
        .data_if_data_rvalid_i  ( data_if.data_rvalid  ),
        .data_if_data_rdata_i   ( data_if.data_rdata   ),

        .irq_i                  ( core_if.irq          ),
        .irq_id_i               ( core_if.irq_id       ),
        .irq_ack_o              ( core_if.irq_ack      ),
        .irq_sec_i              ( core_if.irq_sec      ),
        .sec_lvl_o              ( core_if.sec_lvl      ),

        .debug_req_i            (                      ),
        .debug_gnt_o            (                      ),
        .debug_rvalid_o         (                      ),
        .debug_addr_i           (                      ),
        .debug_we_i             (                      ),
        .debug_wdata_i          (                      ),
        .debug_rdata_o          (                      ),
        .debug_halted_o         (                      ),
        .debug_halt_i           (                      ),
        .debug_resume_i         (                      )
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

    program testbench (core_if core_if, mem_if instr_if);
        initial begin
            uvm_config_db #(virtual core_if)::set(null, "uvm_test_top", "core_if", core_if);
        end
        // logic [7:0] imem [400];
        // logic [63:0] address [$];
        // logic [63:0] addr;
        // // instruction memory
        // initial begin
        //     // read mem file
        //     $readmemh("add_test.v", imem, 64'b0);
        //     $display("Read instruction memory file");
        //     instr_if.mck.data_rdata  <= 32'b0;
        //     // apply stimuli for instruction interface
        //     forever begin
        //         // instr_if.mck.data_rvalid <= 1'b0;
        //         // instr_if.mck.data_gnt    <= 1'b0;

        //         @(instr_if.mck)
        //         instr_if.mck.data_rvalid <= 1'b0;
        //             fork
        //                 imem_read: begin
        //                     // instr_if.mck.data_rvalid <= 1'b0;
        //                     if (instr_if.data_req) begin
        //                         address.push_back(instr_if.mck.address);
        //                     end
        //                 end

        //                 imem_write: begin
        //                     if (address.size() != 0) begin
        //                         instr_if.mck.data_rvalid <= 1'b1;
        //                         addr = address.pop_front();
        //                         instr_if.mck.data_rdata  <= {
        //                             imem[$unsigned(addr + 3)],
        //                             imem[$unsigned(addr + 2)],
        //                             imem[$unsigned(addr + 1)],
        //                             imem[$unsigned(addr + 0)]
        //                             };
        //                         $display("Address: %0h, Data: %0h", addr, {
        //                             imem[$unsigned(addr + 3)],
        //                             imem[$unsigned(addr + 2)],
        //                             imem[$unsigned(addr + 1)],
        //                             imem[$unsigned(addr + 0)]
        //                             });
        //                     end else
        //                         instr_if.mck.data_rvalid <= 1'b0;
        //                 end
        //             join_none

        //     end
        // end
    endprogram

    testbench tb(core_if, instr_if);
endmodule