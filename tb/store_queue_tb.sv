// Author: Florian Zaruba, ETH Zurich
// Date: 28.4.2017
// Description: Store Queue Testbench
//
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

module store_queue_tb;
    import uvm_pkg::*;
    import store_queue_lib_pkg::*;

    logic rst_ni, clk;
    logic store_valid;
    logic slave_data_gnt;

    dcache_if      slave(clk);
    store_queue_if store_queue(clk);

    store_queue dut (
        .clk_i            ( clk                          ),
        .rst_ni           ( rst_ni                       ),
        .flush_i          ( store_queue.flush            ),
        .paddr_o          ( store_queue.check_paddr      ),
        .data_o           ( store_queue.check_data       ),
        .valid_o          ( store_queue.valid            ),
        .be_o             ( store_queue.check_be         ),
        .commit_i         ( store_queue.commit           ),
        .ready_o          ( store_queue.ready            ),
        .valid_i          ( store_queue.store_valid & store_queue.ready ),
        .paddr_i          ( store_queue.store_paddr      ),
        .data_i           ( store_queue.store_data       ),
        .be_i             ( store_queue.store_be         ),

        .address_index_o  ( slave.address_index          ),
        .address_tag_o    ( slave.address_tag            ),
        .data_wdata_o     ( slave.data_wdata             ),
        .data_req_o       ( slave.data_req               ),
        .data_we_o        ( slave.data_we                ),
        .data_be_o        ( slave.data_be                ),
        .kill_req_o       ( slave.kill_req               ),
        .tag_valid_o      ( slave.tag_valid              ),
        .data_gnt_i       ( slave.data_gnt               ),
        .data_rvalid_i    ( slave.data_rvalid            )
    );

    initial begin
        clk = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #10ns clk = ~clk;

        rst_ni = 1'b1;
        forever
            #10ns clk = ~clk;
    end

    program testbench (dcache_if slave, store_queue_if store_queue);
        initial begin
            // register the interfaces
            uvm_config_db #(virtual store_queue_if)::set(null, "uvm_test_top", "store_queue_if", store_queue);
            uvm_config_db #(virtual dcache_if)::set(null, "uvm_test_top", "dcache_if", slave);
            // print the topology
            uvm_top.enable_print_topology = 1;
            // Start UVM test
            run_test();
        end
    endprogram

    testbench tb(slave, store_queue);
endmodule