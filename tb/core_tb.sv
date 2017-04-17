// Author: Florian Zaruba, ETH Zurich
// Date: 15/04/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

import ariane_pkg::*;

module core_tb;


    logic clk_i;
    logic rst_ni;
    logic clock_en_i;
    logic test_en_i;
    logic fetch_enable_i;
    logic core_busy_o;
    logic [63:0] boot_addr_i;
    logic [3:0] core_id_i;
    logic [5:0] cluster_id_i;
    mem_if #(.DATA_WIDTH(32)) instr_if(clk_i);
    mem_if data_if(clk_i);
    logic irq_i;
    logic [4:0] irq_id_i;
    logic irq_ack_o;
    logic irq_sec_i;
    logic sec_lvl_o;
    debug_if debug_if();

    assign boot_addr_i = 64'b0;
    assign test_en_i   = 1'b0;

    ariane dut (
        .clk_i               ( clk_i              ),
        .rst_n               ( rst_ni             ),
        .clock_en_i          ( clock_en_i         ),
        .test_en_i           ( test_en_i          ),
        .fetch_enable_i      ( fetch_enable_i     ),
        .core_busy_o         ( core_busy_o        ),
        .ext_perf_counters_i (  ),
        .boot_addr_i         ( boot_addr_i        ),
        .core_id_i           ( core_id_i          ),
        .cluster_id_i        ( cluster_id_i       ),
        .instr_if            ( instr_if           ),
        .data_if             ( data_if            ),
        .irq_i               ( irq_i              ),
        .irq_id_i            ( irq_id_i           ),
        .irq_ack_o           ( irq_ack_o          ),
        .irq_sec_i           ( irq_sec_i          ),
        .sec_lvl_o           ( sec_lvl_o          ),
        .debug_if            ( debug_if           )
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

    initial begin
        fetch_enable_i = 1'b0;
        wait(rst_ni)
        #1ns fetch_enable_i = 1'b1;

    end

    assign instr_if.data_gnt = instr_if.data_req;

    program testbench (mem_if instr_if);
        logic [7:0] imem [400];
        logic [63:0] address;
        // instruction memory
        initial begin
            // read mem file
            $readmemh("add_test.v", imem, 64'b0);
            $display("Read instruction memory file");
            instr_if.mck.data_rdata  <= 32'b0;
            // apply stimuli for instruction interface
            forever begin
                // instr_if.mck.data_rvalid <= 1'b0;
                // instr_if.mck.data_gnt    <= 1'b0;

                @(instr_if.mck)
                    if (instr_if.mck.data_req) begin
                        // instr_if.mck.data_gnt <= 1'b1;
                        address <= instr_if.mck.address;
                        $display("Time %t, Address %0h", $time, address);
                        // @(instr_if.mck)
                        instr_if.mck.data_rvalid <= 1'b1;
                        instr_if.mck.data_rdata  <= {
                            imem[$unsigned(address + 3)],
                            imem[$unsigned(address + 2)],
                            imem[$unsigned(address + 1)],
                            imem[$unsigned(address + 0)]
                            };
                    end else
                        instr_if.mck.data_rvalid <= 1'b0;

            end
        end
    endprogram

    testbench tb(instr_if);
endmodule