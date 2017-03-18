// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//------------------------------------------------------------------------
// Engineer:       Matthias Baer - baermatt@student.ethz.ch
//
// Additional contributions by:
//                 Igor Loi - igor.loi@unibo.it
//                 Andreas Traber - atraber@student.ethz.ch
//                 Lukas Mueller - lukasmue@student.ethz.ch
//                 Florian Zaruba - zaruabf@ethz.ch
//
// Design Name:    ALU
// Project Name:   RI5CY
// Language:       SystemVerilog
//
// Description:    Minimal version of the ALU, 64-bit compatible
//------------------------------------------------------------------------


import ariane_pkg::*;

module alu
(
  input  logic          clk,
  input  logic          rst_n,

  input  alu_op         operator_i,
  input  logic [63:0]   operand_a_i,
  input  logic [63:0]   operand_b_i,
  input  logic [63:0]   operand_c_i,

  output logic [63:0]   result_o,
  output logic          comparison_result_o,

  output logic          ready_o,
  input  logic          ex_ready_i
);


  logic [63:0] operand_a_rev;
  logic [63:0] operand_a_neg;
  logic [63:0] operand_a_neg_rev;

  assign operand_a_neg = ~operand_a_i;

  // bit reverse operand_a for left shifts and bit counting
  generate
    genvar k;
    for(k = 0; k < 64; k++)
      assign operand_a_rev[k] = operand_a_i[63-k];
  endgenerate

  // bit reverse operand_a_neg for left shifts and bit counting
  generate
    genvar m;
    for(m = 0; m < 64; m++)
      assign operand_a_neg_rev[m] = operand_a_neg[63-m];
  endgenerate

  logic [63:0] operand_b_neg;

  assign operand_b_neg = ~operand_b_i;

  logic [63:0] bmask;

  //--------------------
  // Partitioned added
  //--------------------
  logic        adder_op_b_negate;
  logic [63:0] adder_op_a, adder_op_b;
  logic [63:0] adder_result;

  assign adder_op_b_negate = (operator_i == sub) || (operator_i == subr) ||
                             (operator_i == subu) || (operator_i == subr);

  // prepare operand a
  assign adder_op_a = (operator_i == abs) ? operand_a_neg : operand_a_i;

  // prepare operand b
  assign adder_op_b = adder_op_b_negate ? operand_b_neg : operand_b_i;

  assign adder_result = adder_op_a + adder_op_b + { 63'b0 , adder_op_b_negate };

  //----------
  // Shifts
  //----------
  logic        shift_left;                                    // should we shift left
  logic        shift_arithmetic;

  logic [5:0]  shift_amt_left;                                // amount of shift, if to the left
  logic [5:0]  shift_amt;                                     // amount of shift, to the right
  logic [5:0]  shift_amt_int;                                 // amount of shift, used for the actual shifters
  logic [63:0] shift_op_a;                                    // input of the shifter
  logic [64:0] shift_op_a_ext, shift_right_sign_extended;     // sign extension
  logic [63:0] shift_result;
  logic [63:0] shift_right_result;
  logic [63:0] shift_left_result;

  assign shift_amt = operand_b_i[5:0];

  // by reversing the bits of the input, we also have to reverse the order of shift amounts
  assign shift_amt_left[5:0] = shift_amt[5:0];

  // ALU_FL1 and ALU_CBL are used for the bit counting ops later
  assign shift_left = (operator_i == sll);

  assign shift_arithmetic = (operator_i == sra);

  // choose the bit reversed or the normal input for shift operand a
  assign shift_op_a    = shift_left ? operand_a_rev : operand_a_i;
  assign shift_amt_int = shift_left ? shift_amt_left : shift_amt;

  assign shift_op_a_ext = shift_arithmetic ? {shift_op_a[63], shift_op_a} : {1'b0, shift_op_a};

  assign shift_right_sign_extended = $signed(shift_op_a_ext) >>> shift_amt_int;
  assign shift_right_result = shift_right_sign_extended[63:0];

  // bit reverse the shift_right_result for left shifts
  genvar j;
  generate
    for(j = 0; j < 64; j++)
    begin
      assign shift_left_result[j] = shift_right_result[63-j];
    end
  endgenerate

  assign shift_result = shift_left ? shift_left_result : shift_right_result;

  //----------------
  // Comparisons
  //----------------
  logic [3:0] is_equal;
  logic [3:0] is_greater;  // handles both signed and unsigned forms

  logic [3:0] cmp_signed;

  always_comb
  begin
    cmp_signed = 4'b0;

    unique case (operator_i)
      gts,
      ges,
      lts,
      les,
      slts,
      slets,
      min,
      max,
      abs,
      clip,
      clipu: begin
        cmp_signed[3:0] = 4'b1000;
      end

      default:;
    endcase
  end

  // generate comparison result
  logic [3:0] cmp_result;

  always_comb
  begin
    cmp_result = is_equal;

    unique case (operator_i)
      eq:            cmp_result = is_equal;
      ne:            cmp_result = ~is_equal;
      gts, gtu:  cmp_result = is_greater;
      ges, geu:  cmp_result = is_greater | is_equal;
      lts, slts,
      ltu, sltu: cmp_result = ~(is_greater | is_equal);
      slets,
      sletu,
      les, leu:  cmp_result = ~is_greater;

      default: ;
    endcase
  end

  assign comparison_result_o = cmp_result[3];
  //----------------
  // Result MUX
  //----------------

  always_comb
  begin
    result_o   = 'x;

    unique case (operator_i)
      // Standard Operations
      land:  result_o = operand_a_i & operand_b_i;
      lor:   result_o = operand_a_i | operand_b_i;
      lxor:  result_o = operand_a_i ^ operand_b_i;

      // Shift Operations
      add,
      sub: result_o = adder_result;

      sll,
      srl, sra:  result_o = shift_result;

      // Comparison Operations
      eq,    ne,
      gtu,   geu,
      ltu,   leu,
      gts,   ges,
      lts,   les: begin
          result_o[31:24] = {8{cmp_result[3]}};
          result_o[23:16] = {8{cmp_result[2]}};
          result_o[15: 8] = {8{cmp_result[1]}};
          result_o[ 7: 0] = {8{cmp_result[0]}};
       end
      slts, sltu,
      slets, sletu: result_o = {63'b0, comparison_result_o};

      default: $warning("instruction not supported in basic alu"); // default case to suppress unique warning
    endcase
  end

  assign ready_o = 1'b1;

endmodule
