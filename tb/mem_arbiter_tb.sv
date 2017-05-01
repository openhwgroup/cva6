// Author: Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: Memory Arbiter Testbench
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

module mem_arbiter_tb;

    import uvm_pkg::*;
    // import the main test class
    import mem_arbiter_lib_pkg::*;

    logic rst_ni, clk;

    mem_if master[3](clk);
    mem_if slave(clk);
    // super hack in assigning the wire a value
    // we need to keep all interface signals as wire as
    // the simulator does not now if this interface will be used
    // as an active or passive device
    // only helpful thread so far:
    // https://verificationacademy.com/forums/uvm/getting-multiply-driven-warnings-vsim-passive-agent
    // logic data_gnt_driver = 'z;
    // assign data_gnt = data_gnt_driver & data_req;

    mem_arbiter dut (
        .clk_i          ( clk                             ),
        .rst_ni         ( rst_ni                          ),
        .flush_ready_o  ( flush_ready_o                   ),

        .address_o      ( slave.address                   ),
        .data_wdata_o   ( slave.data_wdata                ),
        .data_req_o     ( slave.data_req                  ),
        .data_we_o      ( slave.data_we                   ),
        .data_be_o      ( slave.data_be                   ),
        .data_gnt_i     ( slave.data_req & slave.data_gnt ),
        .data_rvalid_i  ( slave.data_rvalid               ),
        .data_rdata_i   ( slave.data_rdata                ),

        .address_i      ( {master[2].address,     master[1].address,     master[0].address}      ),
        .data_wdata_i   ( {master[2].data_wdata,  master[1].data_wdata,  master[0].data_wdata}   ),
        .data_req_i     ( {master[2].data_req,    master[1].data_req,    master[0].data_req}     ),
        .data_we_i      ( {master[2].data_we,     master[1].data_we,     master[0].data_we}      ),
        .data_be_i      ( {master[2].data_be,     master[1].data_be,     master[0].data_be}      ),
        .data_gnt_o     ( {master[2].data_gnt,    master[1].data_gnt,    master[0].data_gnt}     ),
        .data_rvalid_o  ( {master[2].data_rvalid, master[1].data_rvalid, master[0].data_rvalid}  ),
        .data_rdata_o   ( {master[2].data_rdata,  master[1].data_rdata,  master[0].data_rdata}   )
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

    program testbench (mem_if master[3], mem_if slave);
        initial begin
            // register the memory interface
            uvm_config_db #(virtual mem_if)::set(null, "uvm_test_top", "mem_if_slave", slave);
            uvm_config_db #(virtual mem_if)::set(null, "uvm_test_top", "mem_if_master0", master[0]);
            uvm_config_db #(virtual mem_if)::set(null, "uvm_test_top", "mem_if_master1", master[1]);
            uvm_config_db #(virtual mem_if)::set(null, "uvm_test_top", "mem_if_master2", master[2]);
            // print the topology
            uvm_top.enable_print_topology = 1;
            // Start UVM test
            run_test();
        end
    endprogram

    testbench tb (master, slave);
endmodule