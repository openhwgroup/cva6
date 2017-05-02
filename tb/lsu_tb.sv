// Author: Florian Zaruba, ETH Zurich
// Date: 02.05.2017
// Description: LSU Testbench
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

module lsu_tb;

    import uvm_pkg::*;
    // import the main test class
    import lsu_lib_pkg::*;
    import ariane_pkg::*;

    logic rst_ni, clk;

    mem_if slave(clk);
    mem_if instr_if(clk);

    lsu dut (
        .clk_i                  ( clk         ),
        .rst_ni                 ( rst_ni      ),
        .flush_i                ( 1'b0        ),
        .operator_i             (             ),
        .operand_a_i            (             ),
        .operand_b_i            (             ),
        .imm_i                  (             ),
        .lsu_ready_o            (             ),
        .lsu_valid_i            (             ),
        .lsu_trans_id_i         (             ),
        .lsu_trans_id_o         (             ),
        .lsu_result_o           (             ),
        .lsu_valid_o            (             ),
        .commit_i               (             ),
        .enable_translation_i   ( 1'b0        ),
        .fetch_req_i            (             ),
        .fetch_gnt_o            (             ),
        .fetch_valid_o          (             ),
        .fetch_err_o            (             ),
        .fetch_vaddr_i          (             ),
        .fetch_rdata_o          (             ),
        .priv_lvl_i             (             ),
        .flag_pum_i             (             ),
        .flag_mxr_i             (             ),
        .pd_ppn_i               (             ),
        .asid_i                 (             ),
        .flush_tlb_i            (             ),
        .instr_if               ( instr_if    ),
        .data_if                ( slave       ),
        .lsu_exception_o        (             )
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

    program testbench (mem_if slave);
        initial begin
            // register the memory interface
            uvm_config_db #(virtual mem_if)::set(null, "uvm_test_top", "mem_if", slave);

            // print the topology
            uvm_top.enable_print_topology = 1;
            // Start UVM test
            run_test();
        end
    endprogram

    testbench tb (slave);
endmodule