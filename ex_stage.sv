import ariane_pkg::*;

module ex_stage (
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low

    input  alu_op                                  operator_i,
    input  logic [63:0]                            operand_a_i,
    input  logic [63:0]                            operand_b_i,

    output logic [63:0]                            alu_result_o,
    output logic                                   comparison_result_o,
    // ALU 1
    output logic                                   alu_ready_o,      // FU is ready
    input  logic                                   alu_valid_i,      // Output is valid
    // LSU
    output logic                                   lsu_ready_o,      // FU is ready
    input  logic                                   lsu_valid_i,      // Output is valid
    // MULT
    output logic                                   mult_ready_o,      // FU is ready
    input  logic                                   mult_valid_i       // Output is valid
);


alu alu_i (
    .operator_i          ( operator_i          ),
    .operand_a_i         ( operand_a_i         ),
    .operand_b_i         ( operand_b_i         ),
    .multdiv_operand_a_i (                     ),
    .multdiv_operand_b_i (                     ),
    .multdiv_en_i        (                     ),
    .adder_result_o      (                     ),
    .adder_result_ext_o  (                     ),
    .result_o            ( alu_result_o        ),
    .comparison_result_o ( comparison_result_o ),
    .is_equal_result_o   (                     )
);

assign alu_ready_o = 1'b1;
// Multiplication

// Load-Store Unit

// pass through


endmodule