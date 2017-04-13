import ariane_pkg::*;

module id_stage (
    input logic          clk_i,    // Clock
    input  logic         rst_ni,  // Asynchronous reset active low
    input  logic         test_en_i, // Test Enable

    input  logic         flush_i,
    // to IF
    input  logic [31:0]  instruction_i,
    input  logic         instruction_valid_i,
    output logic         ready_o,   // id is ready
    output alu_op        operator_o,
    output logic [63:0]  operand_a_o,
    output logic [63:0]  operand_b_o,

    input  logic         alu_ready_i,
    output logic         alu_valid_o,

    input  logic         lsu_ready_i,
    output logic         lsu_valid_o,

    input  logic         mult_ready_i,
    output logic         mult_valid_o,
    // write back port
    input  logic [4:0]   waddr_a_i,
    input  logic [63:0]  wdata_a_i,
    input  logic         we_a_i
);


    logic full_o;
    logic [31:0][$bits(fu_t)-1:0] rd_clobber_o;
    logic [4:0] rs1_i;
    logic [63:0] rs1_o;
    logic rs1_valid_o;
    logic [4:0] rs2_i;
    logic [63:0] rs2_o;
    logic rs2_valid_o;
    scoreboard_entry commit_instr_o;
    logic commit_ack_i;
    scoreboard_entry decoded_instr_i;
    logic decoded_instr_valid_i;
    scoreboard_entry issue_instr_o;
    logic issue_instr_valid_o;
    logic issue_ack_i;
    logic [63:0] pc_i;
    logic [63:0] wdata_i;
    logic wb_valid_i;

// ToDo: Branching logic
assign ready_o = ~full_o;

scoreboard scoreboard_i (
    .clk_i                (clk_i                ),
    .rst_ni               (rst_ni               ),
    .full_o               (full_o               ),
    .flush_i              (flush_i              ),
    .rd_clobber_o         (rd_clobber_o         ),
    .rs1_i                (rs1_i                ),
    .rs1_o                (rs1_o                ),
    .rs1_valid_o          (rs1_valid_o          ),
    .rs2_i                (rs2_i                ),
    .rs2_o                (rs2_o                ),
    .rs2_valid_o          (rs2_valid_o          ),
    .commit_instr_o       (commit_instr_o       ),
    .commit_ack_i         (commit_ack_i         ),
    .decoded_instr_i      (decoded_instr_i      ),
    .decoded_instr_valid_i(decoded_instr_valid_i),
    .issue_instr_o        (issue_instr_o        ),
    .issue_instr_valid_o  (issue_instr_valid_o  ),
    .issue_ack_i          (issue_ack_i          ),
    .pc_i                 (pc_i                 ),
    .wdata_i              (wdata_i              ),
    .wb_valid_i           (wb_valid_i           )
);


issue_read_operands issue_read_operands_i  (
    .clk_i              (clk_i              ),
    .rst_ni             (rst_ni             ),
    .test_en_i          (test_en_i          ),
    .issue_instr_i      (issue_instr_o      ),
    .issue_instr_valid_i(issue_instr_valid_o),
    .issue_ack_o        (issue_ack_i        ),
    .rs1_o              (rs1_i              ),
    .rs1_i              (rs1_o              ),
    .rs1_valid_i        (rs1_valid_o        ),
    .rs2_o              (rs2_i              ),
    .rs2_i              (rs2_o              ),
    .rs2_valid_i        (rs2_valid_o        ),
    .rd_clobber_i       (rd_clobber_o       ),
    .operator_o         (operator_o         ),
    .operand_a_o        (operand_a_o        ),
    .operand_b_o        (operand_b_o        ),
    .alu_ready_i        (alu_ready_i        ),
    .alu_valid_o        (alu_valid_o        ),
    .lsu_ready_i        (lsu_ready_i        ),
    .lsu_valid_o        (lsu_valid_o        ),
    .mult_ready_i       (mult_ready_i       ),
    .mult_valid_o       (mult_valid_o       ),
    .waddr_a_i          (waddr_a_i          ),
    .wdata_a_i          (wdata_a_i          ),
    .we_a_i             (we_a_i             )
);


endmodule