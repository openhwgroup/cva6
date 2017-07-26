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
    output logic                     mult_valid_o,
    output logic                     mult_ready_o,
    output logic [TRANS_ID_BITS-1:0] mult_trans_id_o
);

    // ----------------
    // Mock Multiplier
    // ----------------
    `ifndef SYNTHESIS
    assign mult_valid_o = mult_valid_i;
    assign mult_trans_id_o = trans_id_i;
    assign mult_ready_o = 1'b1;

    always_comb begin : mul_div
        automatic logic [127:0] mult_result;

        result_o = '0;

        case (operator_i)
            // MUL performs an XLEN-bit×XLEN-bit multiplication and places the lower XLEN bits in the destination register
            MUL: begin
                mult_result = operand_a_i * operand_b_i;
                result_o = mult_result[63:0];
            end

            MULH: begin
                mult_result = $signed(operand_a_i) * $signed(operand_b_i);
                result_o = mult_result[127:64];
            end

            MULHU: begin
                mult_result = operand_a_i * operand_b_i;
                result_o = mult_result[127:64];
            end

            MULHSU: begin
                mult_result = $signed(operand_a_i) * $unsigned(operand_b_i);
                result_o = mult_result[127:64];
            end

            MULW:;

            // Divisions
            DIV:;

            DIVU:;

            DIVW:;

            DIVUW:;

            REM:;

            REMU:;

            REMW:;

            REMUW:;
        endcase
    end
    `endif
endmodule
