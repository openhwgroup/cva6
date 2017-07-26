// Author: Pasquale Davide Schiavone <pschiavo@iis.ee.ethz.ch>
//
// Date: 05.06.2017
// Description: Ariane Multiplier
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

import ariane_pkg::*;

module mult
(
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,
    input  logic                     mult_valid_i,
    input  fu_op                     operator_i,
    input  logic [63:0]              operand_a_i,
    input  logic [63:0]              operand_b_i,
    output logic [63:0]              result_o,
    output logic [63:0]              result_o,
    output logic                     mult_valid_o,
    output logic                     mult_ready_o,
    output logic [TRANS_ID_BITS-1:0] mult_trans_id_o
);
    // // MUL and MULH is a two cycle instructions
    // logic signed [63:0]  result_mult;
    // logic signed [63:0]  result_multh;
    // enum logic {FIRST_CYCLE, SECOND_CYCLE} multCS, multNS;
    // logic [TRANS_ID_BITS-1:0] mult_trans_q, mult_trans_n;

    // assign mult_trans_id_o = mult_trans_q;
    // assign result_o        = is_low_part_i ? result_mult : result_multh;

    // mult_datapath
    // mult_dp
    //     (
    //         .operand_a_i    (operand_a_i  ),
    //         .operand_b_i    (operand_b_i  ),
    //         .sign_a_i       (sign_a_i     ),
    //         .sign_b_i       (sign_b_i     ),
    //         .result_low_o   (result_mult  ),
    //         .result_high_o  (result_multh )
    //     );

    // always_comb begin
    //     mult_valid_o = 1'b0;
    //     mult_ready_o = 1'b0;
    //     multNS       = multCS;
    //     mult_trans_n = mult_trans_q;
    //     unique case (multCS)
    //         FIRST_CYCLE: begin
    //             mult_valid_o = 1'b0;
    //             mult_ready_o = 1'b0;
    //             multNS       = mult_valid_i ? SECOND_CYCLE : multCS;
    //         end
    //         SECOND_CYCLE: begin
    //             multNS       = FIRST_CYCLE;
    //             mult_valid_o = 1'b1;
    //             mult_ready_o = 1'b1;
    //         end
    //         default:;
    //     endcase
    // end

    // always_ff @(posedge clk_i or negedge rst_ni) begin
    //     if(~rst_ni) begin
    //         multCS <= FIRST_CYCLE;
    //     end else begin
    //         multCS       <= multNS;
    //         mult_trans_n <= mult_trans_q;
    //     end
    // end

    // Check if we need sign extension

endmodule

// module mult_datapath
// (
//     input  logic [63:0]              operand_a_i,
//     input  logic [63:0]              operand_b_i,
//     input  logic                     sign_a_i,
//     input  logic                     sign_b_i,
//     output logic [63:0]              result_low_o,
//     output logic [63:0]              result_high_o
// );

//     logic signed [129:0] mult_result;
//     logic signed [64:0]  operand_a_ext;
//     logic signed [64:0]  operand_b_ext;

//     assign operand_a_ext  = $signed({sign_a_i & operand_a_i[63], operand_a_i});
//     assign operand_b_ext  = $signed({sign_b_i & operand_b_i[63], operand_b_i});

//     assign mult_result    = operand_a_ext * operand_b_ext;

//     assign result_low_o   = $signed(mult_result[ 63: 0]);
//     assign result_high_o  = $signed(mult_result[127:64]);

// endmodule
