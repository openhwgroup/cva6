// Author: Florian Zaruba, ETH Zurich
// Date: 03/19/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+
module alu_tb;

    import uvm_pkg::*;
    // import the main test class
    import alu_tb_pkg::*;

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
        .clk                    ( clk                       ),
        .rst_n                  ( rstn_i                    ),
        .operator_i             ( alu_if.operator           ),
        .operand_a_i            ( alu_if.operand_a          ),
        .operand_b_i            ( alu_if.operand_b          ),
        .operand_c_i            ( alu_if.operand_c          ),
        .result_o               ( alu_if.result             ),
        .comparison_result_o    ( alu_if.comparison_result  ),
        .ready_o                ( alu_if.valid              ),
        .ex_ready_i             ( alu_if.ready              )
    )

    initial begin
        // print the topology
        uvm_top.enable_print_topology = 1;
        // Start UVM test
        run_test();
    end
endmodule