// Author: Florian Zaruba, ETH Zurich
// Date: 03/19/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
module alu_tb;

    import uvm_pkg::*;
    // import the main test class
    import alu_lib_pkg::*;
    import ariane_pkg::*;

    logic clk;
    logic rstn_i;

    localparam OPERATOR_SIZE = 8;
    localparam OPERAND_SIZE = 64;

    fu_if #(OPERATOR_SIZE, OPERAND_SIZE) alu_if (clk);

    // ------------------------
    // DUT - Device Under Test
    // ------------------------
    alu
    dut
    (
        .operator_i             ( alu_op'(alu_if.operator)  ),
        .operand_a_i            ( alu_if.operand_a          ),
        .operand_b_i            ( alu_if.operand_b          ),
        .result_o               ( alu_if.result             ),
        .comparison_result_o    ( alu_if.comparison_result  ),
        .is_equal_result_o      (  		            ),
        .adder_result_ext_o     (   		            ),
        .adder_result_o         (     			    ),
	.multdiv_en_i           ( 1'b0		            ),
        .multdiv_operand_b_i    ( 65'b0			    ),
	.multdiv_operand_a_i    ( 65'b0		   	    )
    );

    initial begin
	// register the alu itnerface
	uvm_config_db #(virtual fu_if)::set(null, "uvm_test_top", "fu_vif", alu_if);
    end

    initial begin
        clk = 1'b0;
	rstn_i = 1'b0;
	repeat(8) begin
	    #10ns clk = ~clk;
	end
	rstn_i = 1'b1;
	forever begin
	    #10ns clk = ~clk;
	end
    end

    initial begin
        // print the topology
        uvm_top.enable_print_topology = 1;
	    // Start UVM test
        run_test();
    end
endmodule
