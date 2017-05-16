/* Ariane ALU
 * File:   scoreboard.sv
 * Author: Matthias Baer <baermatt@student.ethz.ch>
 * Author: Igor Loi <igor.loi@unibo.it>
 * Author: Andreas Traber <atraber@student.ethz.ch>
 * Author: Lukas Mueller <lukasmue@student.ethz.ch>
 * Author: Florian Zaruba <zaruabf@ethz.ch>
 * Date:   19.3.2017
 *
 * Description:    Minimal version of the ALU, 64-bit compatible
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 */
import ariane_pkg::*;

module alu
(
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,
    input  logic                     alu_valid_i,
    input  fu_op                     operator_i,
    input  logic [63:0]              operand_a_i,
    input  logic [63:0]              operand_b_i,
    output logic [63:0]              result_o,
    output logic                     alu_valid_o,
    output logic                     alu_ready_o,
    output logic [TRANS_ID_BITS-1:0] alu_trans_id_o
);
    // ALU is a single cycle instructions, hence it is always ready

    assign alu_ready_o    = 1'b1;
    assign alu_valid_o    = alu_valid_i;
    assign alu_trans_id_o = trans_id_i;

    logic [63:0] operand_a_rev;
    logic [31:0] operand_a_rev32;
    logic [64:0] operand_b_neg;
    logic [65:0] adder_result_ext_o;
    // bit reverse operand_a for left shifts and bit counting
    generate
      genvar k;
      for(k = 0; k < 64; k++)
        assign operand_a_rev[k] = operand_a_i[63-k];

      for (k = 0; k < 32; k++)
        assign operand_a_rev32[k] = operand_a_i[31-k];
    endgenerate

    // ------
    // Adder
    // ------
    logic        adder_op_b_negate;
    logic [64:0] adder_in_a, adder_in_b;
    logic [63:0] adder_result;

    always_comb begin
      adder_op_b_negate = 1'b0;

      unique case (operator_i)
        // ADDER OPS
        SUB, SUBW: adder_op_b_negate = 1'b1;

        default: ;
      endcase
    end

    // prepare operand a
    assign adder_in_a    = {operand_a_i, 1'b1};

    // prepare operand b
    assign operand_b_neg = {operand_b_i, 1'b0} ^ {65{adder_op_b_negate}};
    assign adder_in_b    =  operand_b_neg ;

    // actual adder
    assign adder_result_ext_o = $unsigned(adder_in_a) + $unsigned(adder_in_b);
    assign adder_result       = adder_result_ext_o[64:1];

    // ---------
    // Shifts
    // ---------

    // TODO: this can probably optimized significantly
    logic        shift_left;          // should we shift left
    logic        shift_arithmetic;

    logic [63:0] shift_amt;           // amount of shift, to the right
    logic [63:0] shift_op_a;          // input of the shifter
    logic [31:0] shift_op_a32;        // input to the 32 bit shift operation

    logic [63:0] shift_result;
    logic [31:0] shift_result32;

    logic [64:0] shift_right_result;
    logic [32:0] shift_right_result32;

    logic [63:0] shift_left_result;
    logic [31:0] shift_left_result32;

    assign shift_amt = operand_b_i;

    assign shift_left = (operator_i == SLL) | (operator_i == SLLW);

    assign shift_arithmetic = (operator_i == SRA) | (operator_i == SRAW);

    // right shifts, we let the synthesizer optimize this
    logic [64:0] shift_op_a_64;
    logic [32:0] shift_op_a_32;

    // choose the bit reversed or the normal input for shift operand a
    assign shift_op_a    = shift_left ? operand_a_rev   : operand_a_i;
    assign shift_op_a32  = shift_left ? operand_a_rev32 : operand_a_i[31:0];

    assign shift_op_a_64 = { shift_arithmetic & shift_op_a[63], shift_op_a};
    assign shift_op_a_32 = { shift_arithmetic & shift_op_a[31], shift_op_a32};

    assign shift_right_result     = $signed(shift_op_a_64) >>> shift_amt[5:0];

    assign shift_right_result32   = $signed(shift_op_a_32) >>> shift_amt[4:0];
    // bit reverse the shift_right_result for left shifts
    genvar j;
    generate
      for(j = 0; j < 64; j++)
        assign shift_left_result[j] = shift_right_result[63-j];

      for(j = 0; j < 32; j++)
        assign shift_left_result32[j] = shift_right_result32[31-j];

    endgenerate

    assign shift_result = shift_left ? shift_left_result : shift_right_result[63:0];
    assign shift_result32 = shift_left ? shift_left_result32 : shift_right_result32[31:0];

    // ------------
    // Comparisons
    // ------------
    logic is_greater_equal;  // handles both signed and unsigned forms
    logic cmp_signed;

    always_comb begin
        cmp_signed = 1'b0;

        if (operator_i == SLTS)
            cmp_signed = 1'b1;
        // Is greater equal
        if ((operand_a_i[63] ^ operand_b_i[63]) == 0)
            is_greater_equal = (adder_result[63] == 0);
        else
            is_greater_equal = operand_a_i[63] ^ (cmp_signed);
    end

    // -----------
    // Result MUX
    // -----------
    always_comb begin
        result_o   = '0;

        unique case (operator_i)
            // Standard Operations
            ANDL:  result_o = operand_a_i & operand_b_i;
            ORL:   result_o = operand_a_i | operand_b_i;
            XORL:  result_o = operand_a_i ^ operand_b_i;

            // Adder Operations
            ADD, SUB: result_o = adder_result;
            // Add word: Ignore the upper bits and sign extend to 64 bit
            ADDW, SUBW: result_o = {{32{adder_result[31]}}, adder_result[31:0]};
            // Shift Operations
            SLL,
            SRL, SRA: result_o = shift_result;
            // Shifts 32 bit
            SLLW,
            SRLW, SRAW: result_o = {{32{shift_result32[31]}}, shift_result32[31:0]};

            // Comparison Operations
            SLTS,  SLTU: result_o = {63'b0, (~is_greater_equal)};

            default: ; // default case to suppress unique warning
        endcase
    end

endmodule
