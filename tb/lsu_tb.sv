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
    lsu_if lsu(clk);

    lsu dut (
        .clk_i                  ( clk                  ),
        .rst_ni                 ( rst_ni               ),
        .flush_i                ( 1'b0                 ),
        .operator_i             ( lsu.operator         ),
        .operand_a_i            ( lsu.operand_a        ),
        .operand_b_i            ( lsu.operand_b        ),
        .imm_i                  ( lsu.imm              ),
        .lsu_ready_o            ( lsu.ready            ),
        .lsu_valid_i            ( lsu.source_valid     ),
        .lsu_trans_id_i         ( lsu.lsu_trans_id_id  ),
        .lsu_trans_id_o         ( lsu.lsu_trans_id_wb  ),
        .lsu_result_o           ( lsu.result           ),
        .lsu_valid_o            ( lsu.result_valid     ),
        .commit_i               ( lsu.commit           ),
        // we are currently no testing the PTW and MMU
        .enable_translation_i   ( 1'b0        ),
        .fetch_req_i            ( 1'b0        ),
        .fetch_gnt_o            (             ),
        .fetch_valid_o          (             ),
        .fetch_err_o            (             ),
        .fetch_vaddr_i          ( 64'b0       ),
        .fetch_rdata_o          (             ),
        .priv_lvl_i             ( PRIV_LVL_M  ),
        .flag_pum_i             ( 1'b0        ),
        .flag_mxr_i             ( 1'b0        ),
        .pd_ppn_i               ( 38'b0       ),
        .asid_i                 ( 1'b0        ),
        .flush_tlb_i            ( 1'b0        ),

        .instr_if_address_o     ( instr_if.address     ),
        .instr_if_data_req_o    ( instr_if.data_req    ),
        .instr_if_data_be_o     ( instr_if.data_be     ),
        .instr_if_data_gnt_i    ( instr_if.data_gnt    ),
        .instr_if_data_rvalid_i ( instr_if.data_rvalid ),
        .instr_if_data_rdata_i  ( instr_if.data_rdata  ),

        .data_if_address_o      ( slave.address        ),
        .data_if_data_wdata_o   ( slave.data_wdata     ),
        .data_if_data_req_o     ( slave.data_req       ),
        .data_if_data_we_o      ( slave.data_we        ),
        .data_if_data_be_o      ( slave.data_be        ),
        // hack to not get a grant without a request
        .data_if_data_gnt_i     ( slave.data_req & slave.data_gnt       ),
        .data_if_data_rvalid_i  ( slave.data_rvalid    ),
        .data_if_data_rdata_i   ( slave.data_rdata     ),

        .lsu_exception_o        ( lsu.exception )
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

    program testbench (mem_if slave, lsu_if lsu);
        initial begin
            // register the memory interface
            uvm_config_db #(virtual mem_if)::set(null, "uvm_test_top", "mem_if", slave);
            uvm_config_db #(virtual lsu_if)::set(null, "uvm_test_top", "lsu_if", lsu);

            // print the topology
            uvm_top.enable_print_topology = 1;
            // Start UVM test
            run_test();
        end
    endprogram

    testbench tb (slave, lsu);
endmodule