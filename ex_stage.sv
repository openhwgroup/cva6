import ariane_pkg::*;

module ex_stage (
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low

    input  fu_op                                   operator_i,
    input  logic [63:0]                            operand_a_i,
    input  logic [63:0]                            operand_b_i,
    input  logic [TRANS_ID_BITS-1:0]               trans_id_i,

    // ALU 1
    output logic                                   alu_ready_o,      // FU is ready
    input  logic                                   alu_valid_i,      // Output is valid
    output logic                                   alu_valid_o,      // ALU result is valid
    output logic [63:0]                            alu_result_o,
    output logic [TRANS_ID_BITS-1:0]               alu_trans_id_o,       // ID of scoreboard entry at which to write back
    output logic                                   comparison_result_o,
    // LSU
    output logic                                   lsu_ready_o,      // FU is ready
    input  logic                                   lsu_valid_i,      // Input is valid
    output logic                                   lsu_valid_o,      // Output is valid
    output logic [63:0]                            lsu_result_o,
    output logic [TRANS_ID_BITS-1:0]               lsu_trans_id_o,
    output logic                                   data_req_o,
    input  logic                                   data_gnt_i,
    input  logic                                   data_rvalid_i,
    input  logic                                   data_err_i,
    output logic [63:0]                            data_addr_o,
    output logic                                   data_we_o,
    output logic [7:0]                             data_be_o,
    output logic [63:0]                            data_wdata_o,
    input  logic [63:0]                            data_rdata_i,
    // MULT
    output logic                                   mult_ready_o,      // FU is ready
    input  logic                                   mult_valid_i       // Output is valid
);


    // ALU is a single cycle instructions, hence it is always ready
    assign alu_ready_o = 1'b1;
    assign alu_valid_o = alu_valid_i;
    assign alu_trans_id_o = trans_id_i;

    alu alu_i (
        .operator_i          ( operator_i          ),
        .operand_a_i         ( operand_a_i         ),
        .operand_b_i         ( operand_b_i         ),
        .adder_result_o      (                     ),
        .adder_result_ext_o  (                     ),
        .result_o            ( alu_result_o        ),
        .comparison_result_o ( comparison_result_o ),
        .is_equal_result_o   (                     )
    );

    // Multiplication

    // Load-Store Unit

    assign lsu_valid_o = 1'b0;
    assign lsu_trans_id_o = trans_id_i;


    exception lsu_exception_o;

    lsu i_lsu (
        .clk_i           ( clk_i           ),
        .rst_ni          ( rst_ni           ),
        .data_req_o      ( data_req_o      ),
        .data_gnt_i      ( data_gnt_i      ),
        .data_rvalid_i   ( data_rvalid_i   ),
        .data_err_i      ( data_err_i      ),
        .data_addr_o     ( data_addr_o     ),
        .data_we_o       ( data_we_o       ),
        .data_be_o       ( data_be_o       ),
        .data_wdata_o    ( data_wdata_o    ),
        .data_rdata_i    ( data_rdata_i    ),
        .operator_i      ( operator_i      ),
        .operand_a_i     ( operand_a_i     ),
        .operand_b_i     ( operand_b_i     ),
        .lsu_ready_o     ( lsu_ready_o     ),
        .lsu_valid_i     ( lsu_valid_i     ),
        .lsu_trans_id_i  ( trans_id_i      ),
        .lsu_trans_id_o  ( lsu_trans_id_o  ),
        .lsu_valid_o     ( lsu_valid_o     ),
        .lsu_exception_o ( lsu_exception_o )  // TODO: exception
    );

    // pass through


endmodule