// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    ALU                                                        //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Arithmetic logic unit of the pipelined processor           //
//                 supports FP-comparisons, classifications if FPU is defined //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import riscv_defines::*;

module riscv_alu
#(
  parameter SHARED_INT_DIV = 0,
  parameter FPU            = 0
)(
  input  logic                     clk,
  input  logic                     rst_n,
  input  logic                     enable_i,
  input  logic [ALU_OP_WIDTH-1:0]  operator_i,
  input  logic [31:0]              operand_a_i,
  input  logic [31:0]              operand_b_i,
  input  logic [31:0]              operand_c_i,

  input  logic [ 1:0]              vector_mode_i,
  input  logic [ 4:0]              bmask_a_i,
  input  logic [ 4:0]              bmask_b_i,
  input  logic [ 1:0]              imm_vec_ext_i,

  input  logic                     is_clpx_i,
  input  logic                     is_subrot_i,
  input  logic [ 1:0]              clpx_shift_i,

  output logic [31:0]              result_o,
  output logic                     comparison_result_o,

  output logic                     ready_o,
  input  logic                     ex_ready_i
);


  logic [31:0] operand_a_rev;
  logic [31:0] operand_a_neg;
  logic [31:0] operand_a_neg_rev;

  assign operand_a_neg = ~operand_a_i;

  // bit reverse operand_a for left shifts and bit counting
  generate
    genvar k;
    for(k = 0; k < 32; k++)
    begin
      assign operand_a_rev[k] = operand_a_i[31-k];
    end
  endgenerate

  // bit reverse operand_a_neg for left shifts and bit counting
  generate
    genvar m;
    for(m = 0; m < 32; m++)
    begin
      assign operand_a_neg_rev[m] = operand_a_neg[31-m];
    end
  endgenerate

  logic [31:0] operand_b_neg;

  assign operand_b_neg = ~operand_b_i;


  logic [5:0]  div_shift;
  logic        div_valid;
  logic [31:0] bmask;

  //////////////////////////////////////////////////////////////////////////////////////////
  //   ____            _   _ _   _                      _      _       _     _            //
  //  |  _ \ __ _ _ __| |_(_) |_(_) ___  _ __   ___  __| |    / \   __| | __| | ___ _ __  //
  //  | |_) / _` | '__| __| | __| |/ _ \| '_ \ / _ \/ _` |   / _ \ / _` |/ _` |/ _ \ '__| //
  //  |  __/ (_| | |  | |_| | |_| | (_) | | | |  __/ (_| |  / ___ \ (_| | (_| |  __/ |    //
  //  |_|   \__,_|_|   \__|_|\__|_|\___/|_| |_|\___|\__,_| /_/   \_\__,_|\__,_|\___|_|    //
  //                                                                                      //
  //////////////////////////////////////////////////////////////////////////////////////////

  logic        adder_op_b_negate;
  logic [31:0] adder_op_a, adder_op_b;
  logic [35:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;
  logic [36:0] adder_result_expanded;


  assign adder_op_b_negate = (operator_i == ALU_SUB) || (operator_i == ALU_SUBR) ||
                             (operator_i == ALU_SUBU) || (operator_i == ALU_SUBUR) || is_subrot_i;

  // prepare operand a
  assign adder_op_a = (operator_i == ALU_ABS) ? operand_a_neg : ( is_subrot_i ? {operand_b_i[15:0], operand_a_i[31:16]} : operand_a_i );

  // prepare operand b
  assign adder_op_b = adder_op_b_negate ? ( is_subrot_i ? ~{operand_a_i[15:0], operand_b_i[31:16]} : operand_b_neg ) : operand_b_i;

  // prepare carry
  always_comb
  begin
    adder_in_a[    0] = 1'b1;
    adder_in_a[ 8: 1] = adder_op_a[ 7: 0];
    adder_in_a[    9] = 1'b1;
    adder_in_a[17:10] = adder_op_a[15: 8];
    adder_in_a[   18] = 1'b1;
    adder_in_a[26:19] = adder_op_a[23:16];
    adder_in_a[   27] = 1'b1;
    adder_in_a[35:28] = adder_op_a[31:24];

    adder_in_b[    0] = 1'b0;
    adder_in_b[ 8: 1] = adder_op_b[ 7: 0];
    adder_in_b[    9] = 1'b0;
    adder_in_b[17:10] = adder_op_b[15: 8];
    adder_in_b[   18] = 1'b0;
    adder_in_b[26:19] = adder_op_b[23:16];
    adder_in_b[   27] = 1'b0;
    adder_in_b[35:28] = adder_op_b[31:24];

    if (adder_op_b_negate || (operator_i == ALU_ABS || operator_i == ALU_CLIP)) begin
      // special case for subtractions and absolute number calculations
      adder_in_b[0] = 1'b1;

      case (vector_mode_i)
        VEC_MODE16: begin
          adder_in_b[18] = 1'b1;
        end

        VEC_MODE8: begin
          adder_in_b[ 9] = 1'b1;
          adder_in_b[18] = 1'b1;
          adder_in_b[27] = 1'b1;
        end
      endcase

    end else begin
      // take care of partitioning the adder for the addition case
      case (vector_mode_i)
        VEC_MODE16: begin
          adder_in_a[18] = 1'b0;
        end

        VEC_MODE8: begin
          adder_in_a[ 9] = 1'b0;
          adder_in_a[18] = 1'b0;
          adder_in_a[27] = 1'b0;
        end
      endcase
    end
  end

  // actual adder
  assign adder_result_expanded = $signed(adder_in_a) + $signed(adder_in_b);
  assign adder_result = {adder_result_expanded[35:28],
                         adder_result_expanded[26:19],
                         adder_result_expanded[17:10],
                         adder_result_expanded[8:1]};


  // normalization stage
  logic [31:0] adder_round_value;
  logic [31:0] adder_round_result;

  assign adder_round_value  = ((operator_i == ALU_ADDR) || (operator_i == ALU_SUBR) ||
                               (operator_i == ALU_ADDUR) || (operator_i == ALU_SUBUR)) ?
                                {1'b0, bmask[31:1]} : '0;
  assign adder_round_result = adder_result + adder_round_value;


  ////////////////////////////////////////
  //  ____  _   _ ___ _____ _____       //
  // / ___|| | | |_ _|  ___|_   _|      //
  // \___ \| |_| || || |_    | |        //
  //  ___) |  _  || ||  _|   | |        //
  // |____/|_| |_|___|_|     |_|        //
  //                                    //
  ////////////////////////////////////////

  logic        shift_left;         // should we shift left
  logic        shift_use_round;
  logic        shift_arithmetic;

  logic [31:0] shift_amt_left;     // amount of shift, if to the left
  logic [31:0] shift_amt;          // amount of shift, to the right
  logic [31:0] shift_amt_int;      // amount of shift, used for the actual shifters
  logic [31:0] shift_amt_norm;     // amount of shift, used for normalization
  logic [31:0] shift_op_a;         // input of the shifter
  logic [31:0] shift_result;
  logic [31:0] shift_right_result;
  logic [31:0] shift_left_result;
  logic [15:0] clpx_shift_ex;

  // shifter is also used for preparing operand for division
  assign shift_amt = div_valid ? div_shift : operand_b_i;

  // by reversing the bits of the input, we also have to reverse the order of shift amounts
  always_comb
  begin
    case(vector_mode_i)
      VEC_MODE16:
      begin
        shift_amt_left[15: 0] = shift_amt[31:16];
        shift_amt_left[31:16] = shift_amt[15: 0];
      end

      VEC_MODE8:
      begin
        shift_amt_left[ 7: 0] = shift_amt[31:24];
        shift_amt_left[15: 8] = shift_amt[23:16];
        shift_amt_left[23:16] = shift_amt[15: 8];
        shift_amt_left[31:24] = shift_amt[ 7: 0];
      end

      default: // VEC_MODE32
      begin
        shift_amt_left[31: 0] = shift_amt[31: 0];
      end
    endcase
  end

  // ALU_FL1 and ALU_CBL are used for the bit counting ops later
  assign shift_left = (operator_i == ALU_SLL) || (operator_i == ALU_BINS) ||
                      (operator_i == ALU_FL1) || (operator_i == ALU_CLB)  ||
                      (operator_i == ALU_DIV) || (operator_i == ALU_DIVU) ||
                      (operator_i == ALU_REM) || (operator_i == ALU_REMU) ||
                      (operator_i == ALU_BREV);

  assign shift_use_round = (operator_i == ALU_ADD)   || (operator_i == ALU_SUB)   ||
                           (operator_i == ALU_ADDR)  || (operator_i == ALU_SUBR)  ||
                           (operator_i == ALU_ADDU)  || (operator_i == ALU_SUBU)  ||
                           (operator_i == ALU_ADDUR) || (operator_i == ALU_SUBUR);

  assign shift_arithmetic = (operator_i == ALU_SRA)  || (operator_i == ALU_BEXT) ||
                            (operator_i == ALU_ADD)  || (operator_i == ALU_SUB)  ||
                            (operator_i == ALU_ADDR) || (operator_i == ALU_SUBR);

  // choose the bit reversed or the normal input for shift operand a
  assign shift_op_a    = shift_left ? operand_a_rev :
                          (shift_use_round ? adder_round_result : operand_a_i);
  assign shift_amt_int = shift_use_round ? shift_amt_norm :
                          (shift_left ? shift_amt_left : shift_amt);

  assign shift_amt_norm = is_clpx_i ? {clpx_shift_ex,clpx_shift_ex} : {4{3'b000, bmask_b_i}};

  assign clpx_shift_ex  = $unsigned(clpx_shift_i);

  // right shifts, we let the synthesizer optimize this
  logic [63:0] shift_op_a_32;

  assign shift_op_a_32 = (operator_i == ALU_ROR) ? {shift_op_a, shift_op_a} : $signed({ {32{shift_arithmetic & shift_op_a[31]}}, shift_op_a});

  always_comb
  begin
    case(vector_mode_i)
      VEC_MODE16:
      begin
          shift_right_result[31:16] = $signed( {shift_arithmetic & shift_op_a[31], shift_op_a[31:16] }) >>> shift_amt_int[19:16];
          shift_right_result[15: 0] = $signed( {shift_arithmetic & shift_op_a[15], shift_op_a[15: 0] }) >>> shift_amt_int[ 3: 0];
      end

      VEC_MODE8:
      begin
          shift_right_result[31:24] = $signed( {shift_arithmetic & shift_op_a[31], shift_op_a[31:24] }) >>> shift_amt_int[26:24];
          shift_right_result[23:16] = $signed( {shift_arithmetic & shift_op_a[23], shift_op_a[23:16] }) >>> shift_amt_int[18:16];
          shift_right_result[15: 8] = $signed( {shift_arithmetic & shift_op_a[15], shift_op_a[15: 8] }) >>> shift_amt_int[10: 8];
          shift_right_result[ 7: 0] = $signed( {shift_arithmetic & shift_op_a[ 7], shift_op_a[ 7: 0] }) >>> shift_amt_int[ 2: 0];
      end

      default: // VEC_MODE32
      begin
          shift_right_result = shift_op_a_32 >> shift_amt_int[4:0];
      end
    endcase; // case (vec_mode_i)
  end

  // bit reverse the shift_right_result for left shifts
  genvar       j;
  generate
    for(j = 0; j < 32; j++)
    begin
      assign shift_left_result[j] = shift_right_result[31-j];
    end
  endgenerate

  assign shift_result = shift_left ? shift_left_result : shift_right_result;


  //////////////////////////////////////////////////////////////////
  //   ____ ___  __  __ ____   _    ____  ___ ____   ___  _   _   //
  //  / ___/ _ \|  \/  |  _ \ / \  |  _ \|_ _/ ___| / _ \| \ | |  //
  // | |  | | | | |\/| | |_) / _ \ | |_) || |\___ \| | | |  \| |  //
  // | |__| |_| | |  | |  __/ ___ \|  _ < | | ___) | |_| | |\  |  //
  //  \____\___/|_|  |_|_| /_/   \_\_| \_\___|____/ \___/|_| \_|  //
  //                                                              //
  //////////////////////////////////////////////////////////////////

  logic [3:0] is_equal;
  logic [3:0] is_greater;     // handles both signed and unsigned forms
  logic [3:0] f_is_greater;   // for floats, only signed and *no vectors*,
                              // inverted for two negative numbers

  // 8-bit vector comparisons, basic building blocks
  logic [3:0]  cmp_signed;
  logic [3:0]  is_equal_vec;
  logic [3:0]  is_greater_vec;
  logic [31:0] operand_b_eq;
  logic        is_equal_clip;


  //second == comparator for CLIP instructions
  always_comb
  begin
    operand_b_eq = operand_b_neg;
    if(operator_i == ALU_CLIPU)
      operand_b_eq = '0;
    else
      operand_b_eq = operand_b_neg;
  end
  assign is_equal_clip = operand_a_i == operand_b_eq;

  always_comb
  begin
    cmp_signed = 4'b0;

    unique case (operator_i)
      ALU_GTS,
      ALU_GES,
      ALU_LTS,
      ALU_LES,
      ALU_SLTS,
      ALU_SLETS,
      ALU_MIN,
      ALU_MAX,
      ALU_ABS,
      ALU_CLIP,
      ALU_CLIPU,
      ALU_FLE,
      ALU_FLT,
      ALU_FMAX,
      ALU_FMIN: begin
        case (vector_mode_i)
          VEC_MODE8:  cmp_signed[3:0] = 4'b1111;
          VEC_MODE16: cmp_signed[3:0] = 4'b1010;
          default:     cmp_signed[3:0] = 4'b1000;
        endcase
      end

      default:;
    endcase
  end

  // generate vector equal and greater than signals, cmp_signed decides if the
  // comparison is done signed or unsigned
  genvar i;
  generate
    for(i = 0; i < 4; i++)
    begin
      assign is_equal_vec[i]   = (operand_a_i[8*i+7:8*i] == operand_b_i[8*i+7:i*8]);
      assign is_greater_vec[i] = $signed({operand_a_i[8*i+7] & cmp_signed[i], operand_a_i[8*i+7:8*i]})
                                  >
                                 $signed({operand_b_i[8*i+7] & cmp_signed[i], operand_b_i[8*i+7:i*8]});
    end
  endgenerate

  // generate the real equal and greater than signals that take the vector
  // mode into account
  always_comb
  begin
    // 32-bit mode
    is_equal[3:0]   = {4{is_equal_vec[3] & is_equal_vec[2] & is_equal_vec[1] & is_equal_vec[0]}};
    is_greater[3:0] = {4{is_greater_vec[3] | (is_equal_vec[3] & (is_greater_vec[2]
                                            | (is_equal_vec[2] & (is_greater_vec[1]
                                             | (is_equal_vec[1] & (is_greater_vec[0]))))))}};

    case(vector_mode_i)
      VEC_MODE16:
      begin
        is_equal[1:0]   = {2{is_equal_vec[0]   & is_equal_vec[1]}};
        is_equal[3:2]   = {2{is_equal_vec[2]   & is_equal_vec[3]}};
        is_greater[1:0] = {2{is_greater_vec[1] | (is_equal_vec[1] & is_greater_vec[0])}};
        is_greater[3:2] = {2{is_greater_vec[3] | (is_equal_vec[3] & is_greater_vec[2])}};
      end

      VEC_MODE8:
      begin
        is_equal[3:0]   = is_equal_vec[3:0];
        is_greater[3:0] = is_greater_vec[3:0];
      end

      default:; // see default assignment
    endcase
  end

  // generate the floating point greater signal, inverted for two negative numbers
  // (but not for identical numbers)
  assign f_is_greater[3:0] = {4{is_greater[3] ^ (operand_a_i[31] & operand_b_i[31] & !is_equal[3])}};

  // generate comparison result
  logic [3:0] cmp_result;
  logic       f_is_qnan;
  logic       f_is_snan;
  logic [3:0] f_is_nan;

  always_comb
  begin
    cmp_result = is_equal;
    f_is_nan   = {4{(f_is_qnan | f_is_snan)}};
    unique case (operator_i)
      ALU_EQ:            cmp_result = is_equal;
      ALU_NE:            cmp_result = ~is_equal;
      ALU_GTS, ALU_GTU:  cmp_result = is_greater;
      ALU_GES, ALU_GEU:  cmp_result = is_greater | is_equal;
      ALU_LTS, ALU_SLTS,
      ALU_LTU, ALU_SLTU: cmp_result = ~(is_greater | is_equal);
      ALU_SLETS,
      ALU_SLETU,
      ALU_LES, ALU_LEU:  cmp_result = ~is_greater;
      ALU_FEQ:           cmp_result = is_equal & ~f_is_nan;
      ALU_FLE:           cmp_result = ~f_is_greater & ~f_is_nan;
      ALU_FLT:           cmp_result = ~(f_is_greater | is_equal) & ~f_is_nan;

      default: ;
    endcase
  end

  assign comparison_result_o = cmp_result[3];


  // min/max/abs handling
  logic [31:0] result_minmax;
  logic [31:0] fp_canonical_nan;
  logic [ 3:0] sel_minmax;
  logic        do_min;
  logic        minmax_is_fp_special;
  logic [31:0] minmax_b;

  assign minmax_b = (operator_i == ALU_ABS) ? adder_result : operand_b_i;

  assign do_min   = (operator_i == ALU_MIN)  || (operator_i == ALU_MINU) ||
                    (operator_i == ALU_CLIP) || (operator_i == ALU_CLIPU) ||
                    (operator_i == ALU_FMIN);

  assign sel_minmax[3:0]      = ((operator_i == ALU_FMIN || operator_i == ALU_FMAX) ? f_is_greater : is_greater) ^ {4{do_min}};

  assign result_minmax[31:24] = (sel_minmax[3] == 1'b1) ? operand_a_i[31:24] : minmax_b[31:24];
  assign result_minmax[23:16] = (sel_minmax[2] == 1'b1) ? operand_a_i[23:16] : minmax_b[23:16];
  assign result_minmax[15: 8] = (sel_minmax[1] == 1'b1) ? operand_a_i[15: 8] : minmax_b[15: 8];
  assign result_minmax[ 7: 0] = (sel_minmax[0] == 1'b1) ? operand_a_i[ 7: 0] : minmax_b[ 7: 0];

  //////////////////////////////////////////////////
  // Float classification
  //////////////////////////////////////////////////
  logic [31:0] fclass_result;

  if (FPU == 1) begin
     logic [7:0]   fclass_exponent;
     logic [22:0]  fclass_mantiassa;
     logic         fclass_ninf;
     logic         fclass_pinf;
     logic         fclass_normal;
     logic         fclass_subnormal;
     logic         fclass_nzero;
     logic         fclass_pzero;
     logic         fclass_is_negative;
     logic         fclass_snan_a;
     logic         fclass_qnan_a;
     logic         fclass_snan_b;
     logic         fclass_qnan_b;

     assign fclass_exponent    = operand_a_i[30:23];
     assign fclass_mantiassa   = operand_a_i[22:0];
     assign fclass_is_negative = operand_a_i[31];

     assign fclass_ninf        = operand_a_i == 32'hFF800000;
     assign fclass_pinf        = operand_a_i == 32'h7F800000;
     assign fclass_normal      = fclass_exponent != 0 && fclass_exponent != 255;
     assign fclass_subnormal   = fclass_exponent == 0 && fclass_mantiassa != 0;
     assign fclass_nzero       = operand_a_i == 32'h80000000;
     assign fclass_pzero       = operand_a_i == 32'h00000000;
     assign fclass_snan_a      = operand_a_i[30:0] == 32'h7fa00000;
     assign fclass_qnan_a      = operand_a_i[30:0] == 32'h7fc00000;
     assign fclass_snan_b      = operand_b_i[30:0] == 32'h7fa00000;
     assign fclass_qnan_b      = operand_b_i[30:0] == 32'h7fc00000;

     assign fclass_result[31:0] = {{22{1'b0}},
                                   fclass_qnan_a,
                                   fclass_snan_a,
                                   fclass_pinf,
                                   (fclass_normal    && !fclass_is_negative),
                                   (fclass_subnormal && !fclass_is_negative),
                                   fclass_pzero,
                                   fclass_nzero,
                                   (fclass_subnormal && fclass_is_negative),
                                   (fclass_normal    && fclass_is_negative),
                                   fclass_ninf};


     // float special cases
     assign f_is_qnan          =  fclass_qnan_a | fclass_qnan_b;
     assign f_is_snan          =  fclass_snan_a | fclass_snan_b;

     assign minmax_is_fp_special = (operator_i == ALU_FMIN || operator_i == ALU_FMAX) & (f_is_snan | f_is_qnan);
     assign fp_canonical_nan     = 32'h7fc00000;
  end else begin // (FPU == 0)
     assign minmax_is_fp_special = '0;
     assign f_is_qnan            = '0;
     assign f_is_snan            = '0;
     assign fclass_result        = '0;
     assign fp_canonical_nan     = '0;
  end


  //////////////////////////////////////////////////
  // Float sign injection
  //////////////////////////////////////////////////
  logic [31:0]  f_sign_inject_result;


   always_comb
     begin
        if (FPU == 1) begin
           f_sign_inject_result[30:0] = operand_a_i[30:0];
           f_sign_inject_result[31]   = operand_a_i[31];

           unique case(operator_i)
             ALU_FKEEP:  f_sign_inject_result[31] = operand_a_i[31];
             ALU_FSGNJ:  f_sign_inject_result[31] = operand_b_i[31];
             ALU_FSGNJN: f_sign_inject_result[31] = !operand_b_i[31];
             ALU_FSGNJX: f_sign_inject_result[31] = operand_a_i[31] ^ operand_b_i[31];
             default: ;
           endcase
        end
        else
          f_sign_inject_result = '0;
     end

  //////////////////////////////////////////////////
  // Clip
  //////////////////////////////////////////////////
  logic [31:0] clip_result;        // result of clip and clip

  always_comb
  begin
    clip_result = result_minmax;
    if(operator_i == ALU_CLIPU) begin
      if(operand_a_i[31] || is_equal_clip) begin
        clip_result = '0;
      end else begin
        clip_result = result_minmax;
      end
    end else begin
      //CLIP
      if(adder_result_expanded[36] || is_equal_clip) begin
        clip_result = operand_b_neg;
      end else begin
        clip_result = result_minmax;
      end
    end

  end

  //////////////////////////////////////////////////
  //  ____  _   _ _   _ _____ _____ _     _____   //
  // / ___|| | | | | | |  ___|  ___| |   | ____|  //
  // \___ \| |_| | | | | |_  | |_  | |   |  _|    //
  //  ___) |  _  | |_| |  _| |  _| | |___| |___   //
  // |____/|_| |_|\___/|_|   |_|   |_____|_____|  //
  //                                              //
  //////////////////////////////////////////////////

  logic [ 3: 0][1:0] shuffle_byte_sel; // select byte in register: 31:24, 23:16, 15:8, 7:0
  logic [ 3: 0]      shuffle_reg_sel;  // select register: rD/rS2 or rS1
  logic [ 1: 0]      shuffle_reg1_sel; // select register rD or rS2 for next stage
  logic [ 1: 0]      shuffle_reg0_sel;
  logic [ 3: 0]      shuffle_through;

  logic [31: 0]      shuffle_r1, shuffle_r0;
  logic [31: 0]      shuffle_r1_in, shuffle_r0_in;
  logic [31: 0]      shuffle_result;
  logic [31: 0]      pack_result;


  always_comb
  begin
    shuffle_reg_sel  = '0;
    shuffle_reg1_sel = 2'b01;
    shuffle_reg0_sel = 2'b10;
    shuffle_through  = '1;

    unique case(operator_i)
      ALU_EXT, ALU_EXTS: begin
        if (operator_i == ALU_EXTS)
          shuffle_reg1_sel = 2'b11;

        if (vector_mode_i == VEC_MODE8) begin
          shuffle_reg_sel[3:1] = 3'b111;
          shuffle_reg_sel[0]   = 1'b0;
        end else begin
          shuffle_reg_sel[3:2] = 2'b11;
          shuffle_reg_sel[1:0] = 2'b00;
        end
      end

      ALU_PCKLO: begin
        shuffle_reg1_sel = 2'b00;

        if (vector_mode_i == VEC_MODE8) begin
          shuffle_through = 4'b0011;
          shuffle_reg_sel = 4'b0001;
        end else begin
          shuffle_reg_sel = 4'b0011;
        end
      end

      ALU_PCKHI: begin
        shuffle_reg1_sel = 2'b00;

        if (vector_mode_i == VEC_MODE8) begin
          shuffle_through = 4'b1100;
          shuffle_reg_sel = 4'b0100;
        end else begin
          shuffle_reg_sel = 4'b0011;
        end
      end

      ALU_SHUF2: begin
        unique case (vector_mode_i)
          VEC_MODE8: begin
            shuffle_reg_sel[3] = ~operand_b_i[26];
            shuffle_reg_sel[2] = ~operand_b_i[18];
            shuffle_reg_sel[1] = ~operand_b_i[10];
            shuffle_reg_sel[0] = ~operand_b_i[ 2];
          end

          VEC_MODE16: begin
            shuffle_reg_sel[3] = ~operand_b_i[17];
            shuffle_reg_sel[2] = ~operand_b_i[17];
            shuffle_reg_sel[1] = ~operand_b_i[ 1];
            shuffle_reg_sel[0] = ~operand_b_i[ 1];
          end
          default:;
        endcase
      end

      ALU_INS: begin
        unique case (vector_mode_i)
          VEC_MODE8: begin
            shuffle_reg0_sel = 2'b00;
            unique case (imm_vec_ext_i)
              2'b00: begin
                shuffle_reg_sel[3:0] = 4'b1110;
              end
              2'b01: begin
                shuffle_reg_sel[3:0] = 4'b1101;
              end
              2'b10: begin
                shuffle_reg_sel[3:0] = 4'b1011;
              end
              2'b11: begin
                shuffle_reg_sel[3:0] = 4'b0111;
              end
              default:;
            endcase
          end
          VEC_MODE16: begin
            shuffle_reg0_sel = 2'b01;
            shuffle_reg_sel[3] = ~imm_vec_ext_i[ 0];
            shuffle_reg_sel[2] = ~imm_vec_ext_i[ 0];
            shuffle_reg_sel[1] =  imm_vec_ext_i[ 0];
            shuffle_reg_sel[0] =  imm_vec_ext_i[ 0];
          end
          default:;
        endcase
      end

      default:;
    endcase
  end

  always_comb
  begin
    shuffle_byte_sel = '0;

    // byte selector
    unique case (operator_i)
      ALU_EXTS,
      ALU_EXT: begin
        unique case (vector_mode_i)
          VEC_MODE8: begin
            shuffle_byte_sel[3] = imm_vec_ext_i[1:0];
            shuffle_byte_sel[2] = imm_vec_ext_i[1:0];
            shuffle_byte_sel[1] = imm_vec_ext_i[1:0];
            shuffle_byte_sel[0] = imm_vec_ext_i[1:0];
          end

          VEC_MODE16: begin
            shuffle_byte_sel[3] = {imm_vec_ext_i[0], 1'b1};
            shuffle_byte_sel[2] = {imm_vec_ext_i[0], 1'b1};
            shuffle_byte_sel[1] = {imm_vec_ext_i[0], 1'b1};
            shuffle_byte_sel[0] = {imm_vec_ext_i[0], 1'b0};
          end

          default:;
        endcase
      end

      ALU_PCKLO: begin
        unique case (vector_mode_i)
          VEC_MODE8: begin
            shuffle_byte_sel[3] = 2'b00;
            shuffle_byte_sel[2] = 2'b00;
            shuffle_byte_sel[1] = 2'b00;
            shuffle_byte_sel[0] = 2'b00;
          end

          VEC_MODE16: begin
            shuffle_byte_sel[3] = 2'b01;
            shuffle_byte_sel[2] = 2'b00;
            shuffle_byte_sel[1] = 2'b01;
            shuffle_byte_sel[0] = 2'b00;
          end

          default:;
        endcase
      end

      ALU_PCKHI: begin
        unique case (vector_mode_i)
          VEC_MODE8: begin
            shuffle_byte_sel[3] = 2'b00;
            shuffle_byte_sel[2] = 2'b00;
            shuffle_byte_sel[1] = 2'b00;
            shuffle_byte_sel[0] = 2'b00;
          end

          VEC_MODE16: begin
            shuffle_byte_sel[3] = 2'b11;
            shuffle_byte_sel[2] = 2'b10;
            shuffle_byte_sel[1] = 2'b11;
            shuffle_byte_sel[0] = 2'b10;
          end

          default:;
        endcase
      end

      ALU_SHUF2,
      ALU_SHUF: begin
        unique case (vector_mode_i)
          VEC_MODE8: begin
            shuffle_byte_sel[3] = operand_b_i[25:24];
            shuffle_byte_sel[2] = operand_b_i[17:16];
            shuffle_byte_sel[1] = operand_b_i[ 9: 8];
            shuffle_byte_sel[0] = operand_b_i[ 1: 0];
          end

          VEC_MODE16: begin
            shuffle_byte_sel[3] = {operand_b_i[16], 1'b1};
            shuffle_byte_sel[2] = {operand_b_i[16], 1'b0};
            shuffle_byte_sel[1] = {operand_b_i[ 0], 1'b1};
            shuffle_byte_sel[0] = {operand_b_i[ 0], 1'b0};
          end
          default:;
        endcase
      end

      ALU_INS: begin
        shuffle_byte_sel[3] = 2'b11;
        shuffle_byte_sel[2] = 2'b10;
        shuffle_byte_sel[1] = 2'b01;
        shuffle_byte_sel[0] = 2'b00;
      end

      default:;
    endcase
  end

  assign shuffle_r0_in = shuffle_reg0_sel[1] ?
                          operand_a_i :
                          (shuffle_reg0_sel[0] ? {2{operand_a_i[15:0]}} : {4{operand_a_i[7:0]}});

  assign shuffle_r1_in = shuffle_reg1_sel[1] ?
                                 {{8{operand_a_i[31]}}, {8{operand_a_i[23]}}, {8{operand_a_i[15]}}, {8{operand_a_i[7]}}} :
                                 (shuffle_reg1_sel[0] ? operand_c_i : operand_b_i);

  assign shuffle_r0[31:24] = shuffle_byte_sel[3][1] ?
                              (shuffle_byte_sel[3][0] ? shuffle_r0_in[31:24] : shuffle_r0_in[23:16]) :
                              (shuffle_byte_sel[3][0] ? shuffle_r0_in[15: 8] : shuffle_r0_in[ 7: 0]);
  assign shuffle_r0[23:16] = shuffle_byte_sel[2][1] ?
                              (shuffle_byte_sel[2][0] ? shuffle_r0_in[31:24] : shuffle_r0_in[23:16]) :
                              (shuffle_byte_sel[2][0] ? shuffle_r0_in[15: 8] : shuffle_r0_in[ 7: 0]);
  assign shuffle_r0[15: 8] = shuffle_byte_sel[1][1] ?
                              (shuffle_byte_sel[1][0] ? shuffle_r0_in[31:24] : shuffle_r0_in[23:16]) :
                              (shuffle_byte_sel[1][0] ? shuffle_r0_in[15: 8] : shuffle_r0_in[ 7: 0]);
  assign shuffle_r0[ 7: 0] = shuffle_byte_sel[0][1] ?
                              (shuffle_byte_sel[0][0] ? shuffle_r0_in[31:24] : shuffle_r0_in[23:16]) :
                              (shuffle_byte_sel[0][0] ? shuffle_r0_in[15: 8] : shuffle_r0_in[ 7: 0]);

  assign shuffle_r1[31:24] = shuffle_byte_sel[3][1] ?
                              (shuffle_byte_sel[3][0] ? shuffle_r1_in[31:24] : shuffle_r1_in[23:16]) :
                              (shuffle_byte_sel[3][0] ? shuffle_r1_in[15: 8] : shuffle_r1_in[ 7: 0]);
  assign shuffle_r1[23:16] = shuffle_byte_sel[2][1] ?
                              (shuffle_byte_sel[2][0] ? shuffle_r1_in[31:24] : shuffle_r1_in[23:16]) :
                              (shuffle_byte_sel[2][0] ? shuffle_r1_in[15: 8] : shuffle_r1_in[ 7: 0]);
  assign shuffle_r1[15: 8] = shuffle_byte_sel[1][1] ?
                              (shuffle_byte_sel[1][0] ? shuffle_r1_in[31:24] : shuffle_r1_in[23:16]) :
                              (shuffle_byte_sel[1][0] ? shuffle_r1_in[15: 8] : shuffle_r1_in[ 7: 0]);
  assign shuffle_r1[ 7: 0] = shuffle_byte_sel[0][1] ?
                              (shuffle_byte_sel[0][0] ? shuffle_r1_in[31:24] : shuffle_r1_in[23:16]) :
                              (shuffle_byte_sel[0][0] ? shuffle_r1_in[15: 8] : shuffle_r1_in[ 7: 0]);

  assign shuffle_result[31:24] = shuffle_reg_sel[3] ? shuffle_r1[31:24] : shuffle_r0[31:24];
  assign shuffle_result[23:16] = shuffle_reg_sel[2] ? shuffle_r1[23:16] : shuffle_r0[23:16];
  assign shuffle_result[15: 8] = shuffle_reg_sel[1] ? shuffle_r1[15: 8] : shuffle_r0[15: 8];
  assign shuffle_result[ 7: 0] = shuffle_reg_sel[0] ? shuffle_r1[ 7: 0] : shuffle_r0[ 7: 0];

  assign pack_result[31:24] = shuffle_through[3] ? shuffle_result[31:24] : operand_c_i[31:24];
  assign pack_result[23:16] = shuffle_through[2] ? shuffle_result[23:16] : operand_c_i[23:16];
  assign pack_result[15: 8] = shuffle_through[1] ? shuffle_result[15: 8] : operand_c_i[15: 8];
  assign pack_result[ 7: 0] = shuffle_through[0] ? shuffle_result[ 7: 0] : operand_c_i[ 7: 0];


  /////////////////////////////////////////////////////////////////////
  //   ____  _ _      ____                  _      ___               //
  //  | __ )(_) |_   / ___|___  _   _ _ __ | |_   / _ \ _ __  ___    //
  //  |  _ \| | __| | |   / _ \| | | | '_ \| __| | | | | '_ \/ __|   //
  //  | |_) | | |_  | |__| (_) | |_| | | | | |_  | |_| | |_) \__ \_  //
  //  |____/|_|\__|  \____\___/ \__,_|_| |_|\__|  \___/| .__/|___(_) //
  //                                                   |_|           //
  /////////////////////////////////////////////////////////////////////

  logic [31:0] ff_input;   // either op_a_i or its bit reversed version
  logic [5:0]  cnt_result; // population count
  logic [5:0]  clb_result; // count leading bits
  logic [4:0]  ff1_result; // holds the index of the first '1'
  logic        ff_no_one;  // if no ones are found
  logic [4:0]  fl1_result; // holds the index of the last '1'
  logic [5:0]  bitop_result; // result of all bitop operations muxed together

  alu_popcnt alu_popcnt_i
  (
    .in_i        ( operand_a_i ),
    .result_o    ( cnt_result  )
  );

  always_comb
  begin
    ff_input = '0;

    case (operator_i)
      ALU_FF1: ff_input = operand_a_i;

      ALU_DIVU,
      ALU_REMU,
      ALU_FL1: ff_input = operand_a_rev;

      ALU_DIV,
      ALU_REM,
      ALU_CLB: begin
        if (operand_a_i[31])
          ff_input = operand_a_neg_rev;
        else
          ff_input = operand_a_rev;
      end
    endcase
  end

  alu_ff alu_ff_i
  (
    .in_i        ( ff_input   ),
    .first_one_o ( ff1_result ),
    .no_ones_o   ( ff_no_one  )
  );

  // special case if ff1_res is 0 (no 1 found), then we keep the 0
  // this is done in the result mux
  assign fl1_result  = 5'd31 - ff1_result;
  assign clb_result  = ff1_result - 5'd1;

  always_comb
  begin
    bitop_result = '0;
    case (operator_i)
      ALU_FF1: bitop_result = ff_no_one ? 6'd32 : {1'b0, ff1_result};
      ALU_FL1: bitop_result = ff_no_one ? 6'd32 : {1'b0, fl1_result};
      ALU_CNT: bitop_result = cnt_result;
      ALU_CLB: begin
        if (ff_no_one) begin
          if (operand_a_i[31])
            bitop_result = 6'd31;
          else
            bitop_result = '0;
        end else begin
          bitop_result = clb_result;
        end
      end
      default:;
    endcase
  end


  ////////////////////////////////////////////////
  //  ____  _ _     __  __             _        //
  // | __ )(_) |_  |  \/  | __ _ _ __ (_)_ __   //
  // |  _ \| | __| | |\/| |/ _` | '_ \| | '_ \  //
  // | |_) | | |_  | |  | | (_| | | | | | |_) | //
  // |____/|_|\__| |_|  |_|\__,_|_| |_|_| .__/  //
  //                                    |_|     //
  ////////////////////////////////////////////////

  logic        extract_is_signed;
  logic        extract_sign;
  logic [31:0] bmask_first, bmask_inv;
  logic [31:0] bextins_and;
  logic [31:0] bextins_result, bclr_result, bset_result;


  // construct bit mask for insert/extract/bclr/bset
  // bmask looks like this 00..0011..1100..00
  assign bmask_first = {32'hFFFFFFFE} << bmask_a_i;
  assign bmask       = (~bmask_first) << bmask_b_i;
  assign bmask_inv   = ~bmask;

  assign bextins_and = (operator_i == ALU_BINS) ? operand_c_i : {32{extract_sign}};

  assign extract_is_signed = (operator_i == ALU_BEXT);
  assign extract_sign = extract_is_signed & shift_result[bmask_a_i];

  assign bextins_result = (bmask & shift_result) | (bextins_and & bmask_inv);

  assign bclr_result = operand_a_i & bmask_inv;
  assign bset_result = operand_a_i | bmask;

  /////////////////////////////////////////////////////////////////////////////////
  //  ____ _____ _______     _____  ________      ________ _____   _____ ______  //
  // |  _ \_   _|__   __|   |  __ \|  ____\ \    / /  ____|  __ \ / ____|  ____| //
  // | |_) || |    | |______| |__) | |__   \ \  / /| |__  | |__) | (___ | |__    //
  // |  _ < | |    | |______|  _  /|  __|   \ \/ / |  __| |  _  / \___ \|  __|   //
  // | |_) || |_   | |      | | \ \| |____   \  /  | |____| | \ \ ____) | |____  //
  // |____/_____|  |_|      |_|  \_\______|   \/   |______|_|  \_\_____/|______| //
  //                                                                             //
  /////////////////////////////////////////////////////////////////////////////////

  logic [31:0] radix_2_rev;
  logic [31:0] radix_4_rev;
  logic [31:0] radix_8_rev;
  logic [31:0] reverse_result;
  logic  [1:0] radix_mux_sel;

  assign radix_mux_sel = bmask_a_i[1:0];

  generate
    // radix-2 bit reverse
    for(j = 0; j < 32; j++)
    begin
      assign radix_2_rev[j] = shift_result[31-j];
    end
    // radix-4 bit reverse
    for(j = 0; j < 16; j++)
    begin
      assign radix_4_rev[2*j+1:2*j] = shift_result[31-j*2:31-j*2-1];
    end
    // radix-8 bit reverse
    for(j = 0; j < 10; j++)
    begin
      assign radix_8_rev[3*j+2:3*j] = shift_result[31-j*3:31-j*3-2];
    end
    assign radix_8_rev[31:30] = 2'b0;
  endgenerate

  always_comb
  begin
    reverse_result = '0;

    unique case (radix_mux_sel)
      2'b00: reverse_result = radix_2_rev;
      2'b01: reverse_result = radix_4_rev;
      2'b10: reverse_result = radix_8_rev;

      default: reverse_result = radix_2_rev;
    endcase
  end

  ////////////////////////////////////////////////////
  //  ____ _____     __     __  ____  _____ __  __  //
  // |  _ \_ _\ \   / /    / / |  _ \| ____|  \/  | //
  // | | | | | \ \ / /    / /  | |_) |  _| | |\/| | //
  // | |_| | |  \ V /    / /   |  _ <| |___| |  | | //
  // |____/___|  \_/    /_/    |_| \_\_____|_|  |_| //
  //                                                //
  ////////////////////////////////////////////////////

   logic [31:0] result_div;
   logic        div_ready;

   if (SHARED_INT_DIV == 1) begin

      assign result_div = '0;
      assign div_ready = '1;
      assign div_valid = '0;

   end else begin : int_div

      logic        div_signed;
      logic        div_op_a_signed;
      logic        div_op_b_signed;
      logic [5:0]  div_shift_int;

      assign div_signed = operator_i[0];

      assign div_op_a_signed = operand_a_i[31] & div_signed;
      assign div_op_b_signed = operand_b_i[31] & div_signed;

      assign div_shift_int = ff_no_one ? 6'd31 : clb_result;
      assign div_shift = div_shift_int + (div_op_a_signed ? 6'd0 : 6'd1);

      assign div_valid = enable_i & ((operator_i == ALU_DIV) || (operator_i == ALU_DIVU) ||
                         (operator_i == ALU_REM) || (operator_i == ALU_REMU));


      // inputs A and B are swapped
      riscv_alu_div div_i
        (
         .Clk_CI       ( clk               ),
         .Rst_RBI      ( rst_n             ),

         // input IF
         .OpA_DI       ( operand_b_i       ),
         .OpB_DI       ( shift_left_result ),
         .OpBShift_DI  ( div_shift         ),
         .OpBIsZero_SI ( (cnt_result == 0) ),

         .OpBSign_SI   ( div_op_a_signed   ),
         .OpCode_SI    ( operator_i[1:0]   ),

         .Res_DO       ( result_div        ),

         // Hand-Shake
         .InVld_SI     ( div_valid         ),
         .OutRdy_SI    ( ex_ready_i        ),
         .OutVld_SO    ( div_ready         )
         );
   end

  ////////////////////////////////////////////////////////
  //   ____                 _ _     __  __              //
  //  |  _ \ ___  ___ _   _| | |_  |  \/  |_   ___  __  //
  //  | |_) / _ \/ __| | | | | __| | |\/| | | | \ \/ /  //
  //  |  _ <  __/\__ \ |_| | | |_  | |  | | |_| |>  <   //
  //  |_| \_\___||___/\__,_|_|\__| |_|  |_|\__,_/_/\_\  //
  //                                                    //
  ////////////////////////////////////////////////////////

  always_comb
  begin
    result_o   = '0;

    unique case (operator_i)
      // Standard Operations
      ALU_AND:  result_o = operand_a_i & operand_b_i;
      ALU_OR:   result_o = operand_a_i | operand_b_i;
      ALU_XOR:  result_o = operand_a_i ^ operand_b_i;

      // Shift Operations
      ALU_ADD, ALU_ADDR, ALU_ADDU, ALU_ADDUR,
      ALU_SUB, ALU_SUBR, ALU_SUBU, ALU_SUBUR,
      ALU_SLL,
      ALU_SRL, ALU_SRA,
      ALU_ROR:  result_o = shift_result;

      // bit manipulation instructions
      ALU_BINS,
      ALU_BEXT,
      ALU_BEXTU: result_o = bextins_result;

      ALU_BCLR:  result_o = bclr_result;
      ALU_BSET:  result_o = bset_result;

      // Bit reverse instruction
      ALU_BREV:  result_o = reverse_result;

      // pack and shuffle operations
      ALU_SHUF,  ALU_SHUF2,
      ALU_PCKLO, ALU_PCKHI,
      ALU_EXT,   ALU_EXTS,
      ALU_INS: result_o = pack_result;

      // Min/Max/Ins
      ALU_MIN, ALU_MINU,
      ALU_MAX, ALU_MAXU,
      ALU_FMIN,
      ALU_FMAX: result_o = minmax_is_fp_special ? fp_canonical_nan : result_minmax;

      //Abs/Cplxconj , ABS is used to do 0 - A for Cplxconj
      ALU_ABS:  result_o = is_clpx_i ? {adder_result[31:16], operand_a_i[15:0]} : result_minmax;

      ALU_CLIP, ALU_CLIPU: result_o = clip_result;

      // Comparison Operations
      ALU_EQ,    ALU_NE,
      ALU_GTU,   ALU_GEU,
      ALU_LTU,   ALU_LEU,
      ALU_GTS,   ALU_GES,
      ALU_LTS,   ALU_LES: begin
          result_o[31:24] = {8{cmp_result[3]}};
          result_o[23:16] = {8{cmp_result[2]}};
          result_o[15: 8] = {8{cmp_result[1]}};
          result_o[ 7: 0] = {8{cmp_result[0]}};
       end
      // Non-vector comparisons
      ALU_FEQ,   ALU_FLT,
      ALU_FLE,
      ALU_SLTS,  ALU_SLTU,
      ALU_SLETS, ALU_SLETU: result_o = {31'b0, comparison_result_o};

      ALU_FF1, ALU_FL1, ALU_CLB, ALU_CNT: result_o = {26'h0, bitop_result[5:0]};

      // Division Unit Commands
      ALU_DIV, ALU_DIVU,
      ALU_REM, ALU_REMU: result_o = result_div;

      // fclass
      ALU_FCLASS: result_o = fclass_result;

      // float sign injection
      ALU_FSGNJ, ALU_FSGNJN,
      ALU_FSGNJX, ALU_FKEEP: result_o = f_sign_inject_result;

      default: ; // default case to suppress unique warning
    endcase
  end

  assign ready_o = div_ready;

endmodule

module alu_ff
#(
  parameter LEN = 32
)
(
  input  logic [LEN-1:0]         in_i,

  output logic [$clog2(LEN)-1:0] first_one_o,
  output logic                   no_ones_o
);

  localparam NUM_LEVELS = $clog2(LEN);

  logic [LEN-1:0] [NUM_LEVELS-1:0]           index_lut;
  logic [2**NUM_LEVELS-1:0]                  sel_nodes;
  logic [2**NUM_LEVELS-1:0] [NUM_LEVELS-1:0] index_nodes;


  //////////////////////////////////////////////////////////////////////////////
  // generate tree structure
  //////////////////////////////////////////////////////////////////////////////

  generate
    genvar j;
    for (j = 0; j < LEN; j++) begin
      assign index_lut[j] = $unsigned(j);
    end
  endgenerate

  generate
    genvar k;
    genvar l;
    genvar level;
    for (level = 0; level < NUM_LEVELS; level++) begin
    //------------------------------------------------------------
    if (level < NUM_LEVELS-1) begin
      for (l = 0; l < 2**level; l++) begin
        assign sel_nodes[2**level-1+l]   = sel_nodes[2**(level+1)-1+l*2] | sel_nodes[2**(level+1)-1+l*2+1];
        assign index_nodes[2**level-1+l] = (sel_nodes[2**(level+1)-1+l*2] == 1'b1) ?
                                           index_nodes[2**(level+1)-1+l*2] : index_nodes[2**(level+1)-1+l*2+1];
      end
    end
    //------------------------------------------------------------
    if (level == NUM_LEVELS-1) begin
      for (k = 0; k < 2**level; k++) begin
        // if two successive indices are still in the vector...
        if (k * 2 < LEN-1) begin
          assign sel_nodes[2**level-1+k]   = in_i[k*2] | in_i[k*2+1];
          assign index_nodes[2**level-1+k] = (in_i[k*2] == 1'b1) ? index_lut[k*2] : index_lut[k*2+1];
        end
        // if only the first index is still in the vector...
        if (k * 2 == LEN-1) begin
          assign sel_nodes[2**level-1+k]   = in_i[k*2];
          assign index_nodes[2**level-1+k] = index_lut[k*2];
        end
        // if index is out of range
        if (k * 2 > LEN-1) begin
          assign sel_nodes[2**level-1+k]   = 1'b0;
          assign index_nodes[2**level-1+k] = '0;
        end
      end
    end
    //------------------------------------------------------------
    end
  endgenerate

  //////////////////////////////////////////////////////////////////////////////
  // connect output
  //////////////////////////////////////////////////////////////////////////////

  assign first_one_o = index_nodes[0];
  assign no_ones_o   = ~sel_nodes[0];

endmodule

// count the number of '1's in a word
module alu_popcnt
(
  input  logic [31:0]  in_i,
  output logic [5: 0]  result_o
);

  logic [15:0][1:0] cnt_l1;
  logic [ 7:0][2:0] cnt_l2;
  logic [ 3:0][3:0] cnt_l3;
  logic [ 1:0][4:0] cnt_l4;

  genvar      l, m, n, p;
  generate for(l = 0; l < 16; l++)
    begin
      assign cnt_l1[l] = {1'b0, in_i[2*l]} + {1'b0, in_i[2*l + 1]};
    end
  endgenerate

  generate for(m = 0; m < 8; m++)
    begin
      assign cnt_l2[m] = {1'b0, cnt_l1[2*m]} + {1'b0, cnt_l1[2*m + 1]};
    end
  endgenerate

  generate for(n = 0; n < 4; n++)
    begin
      assign cnt_l3[n] = {1'b0, cnt_l2[2*n]} + {1'b0, cnt_l2[2*n + 1]};
    end
  endgenerate

  generate for(p = 0; p < 2; p++)
    begin
      assign cnt_l4[p] = {1'b0, cnt_l3[2*p]} + {1'b0, cnt_l3[2*p + 1]};
    end
  endgenerate

  assign result_o = {1'b0, cnt_l4[0]} + {1'b0, cnt_l4[1]};

endmodule
