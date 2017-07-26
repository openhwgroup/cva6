// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
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

    function automatic logic [63:0] sign_extend (logic [31:0] operand);
        return {{32{operand[31]}}, operand[31:0]};
    endfunction

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
                mult_result = $signed({operand_a_i[63], operand_a_i}) * $signed({1'b0, operand_b_i});
                result_o = mult_result[127:64];
            end

            MULW: begin
                mult_result[63:0] = $signed(operand_a_i[31:0]) * $signed(operand_b_i[31:0]);
                // sign extend the result
                result_o = sign_extend(mult_result[31:0]);
            end

            // Divisions
            DIV: begin
                result_o = $signed(operand_a_i) / $signed(operand_b_i);
                // division by zero
                // set all bits
                if (operand_b_i == '0)
                    result_o = -1;
            end

            DIVU: begin
                result_o = operand_a_i / operand_b_i;
                // division by zero
                // set all bits
                if (operand_b_i == '0)
                    result_o = -1;
            end

            DIVW: begin
                result_o = sign_extend($signed(operand_a_i[31:0]) / $signed(operand_b_i[31:0]));
                // division by zero
                // set all bits
                if (operand_b_i == '0)
                    result_o = -1;
            end

            DIVUW: begin
                result_o = sign_extend(operand_a_i[31:0] / operand_b_i[31:0]);
                // division by zero
                // set all bits
                if (operand_b_i == '0)
                    result_o = -1;
            end

            REM: begin
                result_o = $signed(operand_a_i) % $signed(operand_b_i);
                // division by zero
                if (operand_b_i == '0)
                    result_o = operand_a_i;
            end

            REMU: begin
                result_o = operand_a_i % operand_b_i;
                // division by zero
                if (operand_b_i == '0)
                    result_o = operand_a_i;
            end

            REMW: begin
                result_o = sign_extend($signed(operand_a_i[31:0]) % $signed(operand_b_i[31:0]));
                // division by zero
                if (operand_b_i == '0)
                    result_o = operand_a_i;
            end

            REMUW: begin
                result_o = sign_extend(operand_a_i[31:0] % operand_b_i[31:0]);
                // division by zero
                if (operand_b_i == '0)
                    result_o = operand_a_i;
            end
        endcase
    end
    `endif
endmodule
