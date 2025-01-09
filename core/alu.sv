// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Matthias Baer <baermatt@student.ethz.ch>
// Author: Igor Loi <igor.loi@unibo.it>
// Author: Andreas Traber <atraber@student.ethz.ch>
// Author: Lukas Mueller <lukasmue@student.ethz.ch>
// Author: Florian Zaruba <zaruabf@iis.ee.ethz.ch>
//
// Date: 19.03.2017
// Description: Ariane ALU based on RI5CY's ALU


module alu
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter bit HasBranch = 1'b1,
    parameter type fu_data_t = logic
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // FU data needed to execute instruction - ISSUE_STAGE
    input fu_data_t fu_data_i,
    // ALU result - ISSUE_STAGE
    output logic [CVA6Cfg.XLEN-1:0] result_o,
    // ALU branch compare result - branch_unit
    output logic alu_branch_res_o
);

  logic [CVA6Cfg.XLEN-1:0] operand_a_rev;
  logic [            31:0] operand_a_rev32;
  logic [  CVA6Cfg.XLEN:0] operand_b_neg;
  logic [CVA6Cfg.XLEN+1:0] adder_result_ext_o;
  logic                    less;  // handles both signed and unsigned forms
  logic [            31:0] rolw;  // Rotate Left Word
  logic [            31:0] rorw;  // Rotate Right Word
  logic [31:0] orcbw, rev8w;
  logic [  $clog2(CVA6Cfg.XLEN) : 0] cpop;  // Count Population
  logic [$clog2(CVA6Cfg.XLEN)-1 : 0] lz_tz_count;  // Count Leading Zeros
  logic [                       4:0] lz_tz_wcount;  // Count Leading Zeros Word
  logic lz_tz_empty, lz_tz_wempty;
  logic [CVA6Cfg.XLEN-1:0] orcbw_result, rev8w_result;

  logic [CVA6Cfg.XLEN-1:0] brev8_reversed;
  logic [            31:0] unzip_gen;
  logic [            31:0] zip_gen;
  logic [CVA6Cfg.XLEN-1:0] xperm8_result;
  logic [CVA6Cfg.XLEN-1:0] xperm4_result;
  //logic [             7:0] sbox_in;
  //logic [             7:0] sbox_out;
  //logic [            31:0] mix_out;
  logic [            63:0] sr;
  //logic [            31:0] aes32esi_gen;
  //logic [            31:0] aes32esmi_gen;
  logic [            63:0] aes64es_gen;
  logic [            63:0] aes64esm_gen;
  //logic [            63:0] aes64ks1i_gen;
  logic [            63:0] aes64ks2_gen;
  // bit reverse operand_a for left shifts and bit counting
  generate
    genvar k;
    for (k = 0; k < CVA6Cfg.XLEN; k++)
      assign operand_a_rev[k] = fu_data_i.operand_a[CVA6Cfg.XLEN-1-k];

    for (k = 0; k < 32; k++) assign operand_a_rev32[k] = fu_data_i.operand_a[31-k];
  endgenerate

  // ------
  // Adder
  // ------
  logic adder_op_b_negate;
  logic adder_z_flag;
  logic [CVA6Cfg.XLEN:0] adder_in_a, adder_in_b;
  logic [CVA6Cfg.XLEN-1:0] adder_result;
  logic [CVA6Cfg.XLEN-1:0] operand_a_bitmanip, bit_indx;

  assign adder_op_b_negate = fu_data_i.operation inside {EQ, NE, SUB, SUBW, ANDN, ORN, XNOR};

  always_comb begin
    operand_a_bitmanip = fu_data_i.operand_a;

    if (CVA6Cfg.RVB) begin
      if (CVA6Cfg.IS_XLEN64) begin
        unique case (fu_data_i.operation)
          SH1ADDUW:           operand_a_bitmanip = fu_data_i.operand_a[31:0] << 1;
          SH2ADDUW:           operand_a_bitmanip = fu_data_i.operand_a[31:0] << 2;
          SH3ADDUW:           operand_a_bitmanip = fu_data_i.operand_a[31:0] << 3;
          CTZW:               operand_a_bitmanip = operand_a_rev32;
          ADDUW, CPOPW, CLZW: operand_a_bitmanip = fu_data_i.operand_a[31:0];
          default:            ;
        endcase
      end
      unique case (fu_data_i.operation)
        SH1ADD:  operand_a_bitmanip = fu_data_i.operand_a << 1;
        SH2ADD:  operand_a_bitmanip = fu_data_i.operand_a << 2;
        SH3ADD:  operand_a_bitmanip = fu_data_i.operand_a << 3;
        CTZ:     operand_a_bitmanip = operand_a_rev;
        default: ;
      endcase
    end
  end

  // prepare operand a
  assign adder_in_a         = {operand_a_bitmanip, 1'b1};

  // prepare operand b
  assign operand_b_neg      = {fu_data_i.operand_b, 1'b0} ^ {CVA6Cfg.XLEN + 1{adder_op_b_negate}};
  assign adder_in_b         = operand_b_neg;

  // actual adder
  assign adder_result_ext_o = adder_in_a + adder_in_b;
  assign adder_result       = adder_result_ext_o[CVA6Cfg.XLEN:1];
  assign adder_z_flag       = ~|adder_result;

  // get the right branch comparison result
  if (HasBranch) begin
    always_comb begin : branch_resolve
      // set comparison by default
      case (fu_data_i.operation)
        EQ:       alu_branch_res_o = adder_z_flag;
        NE:       alu_branch_res_o = ~adder_z_flag;
        LTS, LTU: alu_branch_res_o = less;
        GES, GEU: alu_branch_res_o = ~less;
        default:  alu_branch_res_o = 1'b1;
      endcase
    end
  end else begin
    assign alu_branch_res_o = 1'b0;
  end

  // ---------
  // Shifts
  // ---------

  // TODO: this can probably optimized significantly
  logic                    shift_left;  // should we shift left
  logic                    shift_arithmetic;

  logic [CVA6Cfg.XLEN-1:0] shift_amt;  // amount of shift, to the right
  logic [CVA6Cfg.XLEN-1:0] shift_op_a;  // input of the shifter
  logic [            31:0] shift_op_a32;  // input to the 32 bit shift operation

  logic [CVA6Cfg.XLEN-1:0] shift_result;
  logic [            31:0] shift_result32;

  logic [  CVA6Cfg.XLEN:0] shift_right_result;
  logic [            32:0] shift_right_result32;

  logic [CVA6Cfg.XLEN-1:0] shift_left_result;
  logic [            31:0] shift_left_result32;

  assign shift_amt = fu_data_i.operand_b;

  assign shift_left = (fu_data_i.operation == SLL) | (CVA6Cfg.IS_XLEN64 && fu_data_i.operation == SLLW);

  assign shift_arithmetic = (fu_data_i.operation == SRA) | (CVA6Cfg.IS_XLEN64 && fu_data_i.operation == SRAW);

  // right shifts, we let the synthesizer optimize this
  logic [CVA6Cfg.XLEN:0] shift_op_a_64;
  logic [32:0] shift_op_a_32;

  // choose the bit reversed or the normal input for shift operand a
  assign shift_op_a           = shift_left ? operand_a_rev : fu_data_i.operand_a;
  assign shift_op_a32         = shift_left ? operand_a_rev32 : fu_data_i.operand_a[31:0];

  assign shift_op_a_64        = {shift_arithmetic & shift_op_a[CVA6Cfg.XLEN-1], shift_op_a};
  assign shift_op_a_32        = {shift_arithmetic & shift_op_a[31], shift_op_a32};

  assign shift_right_result   = $unsigned($signed(shift_op_a_64) >>> shift_amt[5:0]);

  assign shift_right_result32 = $unsigned($signed(shift_op_a_32) >>> shift_amt[4:0]);
  // bit reverse the shift_right_result for left shifts
  genvar j;
  generate
    for (j = 0; j < CVA6Cfg.XLEN; j++)
      assign shift_left_result[j] = shift_right_result[CVA6Cfg.XLEN-1-j];

    for (j = 0; j < 32; j++) assign shift_left_result32[j] = shift_right_result32[31-j];

  endgenerate

  assign shift_result   = shift_left ? shift_left_result : shift_right_result[CVA6Cfg.XLEN-1:0];
  assign shift_result32 = shift_left ? shift_left_result32 : shift_right_result32[31:0];

  // ------------
  // Comparisons
  // ------------

  always_comb begin
    logic sgn;
    sgn = 1'b0;

    if ((fu_data_i.operation == SLTS) ||
            (fu_data_i.operation == LTS)  ||
            (fu_data_i.operation == GES)  ||
            (fu_data_i.operation == MAX)  ||
            (fu_data_i.operation == MIN))
      sgn = 1'b1;

    less = ($signed({sgn & fu_data_i.operand_a[CVA6Cfg.XLEN-1], fu_data_i.operand_a}) <
            $signed({sgn & fu_data_i.operand_b[CVA6Cfg.XLEN-1], fu_data_i.operand_b}));
  end

  if (CVA6Cfg.RVB) begin : gen_bitmanip
    // Count Population + Count population Word

    popcount #(
        .INPUT_WIDTH(CVA6Cfg.XLEN)
    ) i_cpop_count (
        .data_i    (operand_a_bitmanip),
        .popcount_o(cpop)
    );

    // Count Leading/Trailing Zeros
    // 64b
    lzc #(
        .WIDTH(CVA6Cfg.XLEN),
        .MODE (1)
    ) i_clz_64b (
        .in_i(operand_a_bitmanip),
        .cnt_o(lz_tz_count),
        .empty_o(lz_tz_empty)
    );
    if (CVA6Cfg.IS_XLEN64) begin
      //32b
      lzc #(
          .WIDTH(32),
          .MODE (1)
      ) i_clz_32b (
          .in_i(operand_a_bitmanip[31:0]),
          .cnt_o(lz_tz_wcount),
          .empty_o(lz_tz_wempty)
      );
    end
  end

  if (CVA6Cfg.RVB) begin : gen_orcbw_rev8w_results
    assign orcbw = {
      {8{|fu_data_i.operand_a[31:24]}},
      {8{|fu_data_i.operand_a[23:16]}},
      {8{|fu_data_i.operand_a[15:8]}},
      {8{|fu_data_i.operand_a[7:0]}}
    };
    assign rev8w = {
      {fu_data_i.operand_a[7:0]},
      {fu_data_i.operand_a[15:8]},
      {fu_data_i.operand_a[23:16]},
      {fu_data_i.operand_a[31:24]}
    };
    if (CVA6Cfg.IS_XLEN64) begin : gen_64b
      assign orcbw_result = {
        {8{|fu_data_i.operand_a[63:56]}},
        {8{|fu_data_i.operand_a[55:48]}},
        {8{|fu_data_i.operand_a[47:40]}},
        {8{|fu_data_i.operand_a[39:32]}},
        orcbw
      };
      assign rev8w_result = {
        rev8w,
        {fu_data_i.operand_a[39:32]},
        {fu_data_i.operand_a[47:40]},
        {fu_data_i.operand_a[55:48]},
        {fu_data_i.operand_a[63:56]}
      };
    end else begin : gen_32b
      assign orcbw_result = orcbw;
      assign rev8w_result = rev8w;
    end
  end

  // ZKN gen block
  if (CVA6Cfg.ZKN && CVA6Cfg.RVB) begin : zkn_gen_block
    // AES MixColumns Forward
    function [31:0] aes_mixcolumn_fwd(input [31:0] x);
      reg [7:0] s0, s1, s2, s3;
      reg [7:0] b0, b1, b2, b3;
      begin
        s0 = x[7:0];
        s1 = x[15:8];
        s2 = x[23:16];
        s3 = x[31:24];
        b0 = ((s0 << 1) ^ ((s0[7]) ? 8'h1B : 8'h00)) ^ (((s1 << 1) ^ ((s1[7]) ? 8'h1B : 8'h00)) ^ s1) ^ s2 ^ s3;
        b1 = s0 ^ ((s1 << 1) ^ ((s1[7]) ? 8'h1B : 8'h00)) ^ (((s2 << 1) ^ ((s2[7]) ? 8'h1B : 8'h00)) ^ s2) ^ s3;
        b2 = s0 ^ s1 ^ ((s2 << 1) ^ ((s2[7]) ? 8'h1B : 8'h00)) ^ (((s3 << 1) ^ ((s3[7]) ? 8'h1B : 8'h00)) ^ s3);
        b3 = (((s0 << 1) ^ ((s0[7]) ? 8'h1B : 8'h00)) ^ s0) ^ s1 ^ s2 ^ ((s3 << 1) ^ ((s3[7]) ? 8'h1B : 8'h00));
        aes_mixcolumn_fwd = {b3, b2, b1, b0};
      end
    endfunction
    // AES Sbox Forward
    function [7:0] aes_sbox_fwd(input [7:0] si);
    case (si)
    8'h00: aes_sbox_fwd = 8'h63; 8'h01: aes_sbox_fwd = 8'h7C; 8'h02: aes_sbox_fwd = 8'h77; 8'h03: aes_sbox_fwd = 8'h7B; 8'h04: aes_sbox_fwd = 8'hF2; 8'h05: aes_sbox_fwd = 8'h6B;
    8'h06: aes_sbox_fwd = 8'h6F; 8'h07: aes_sbox_fwd = 8'hC5; 8'h08: aes_sbox_fwd = 8'h30; 8'h09: aes_sbox_fwd = 8'h01; 8'h0A: aes_sbox_fwd = 8'h67; 8'h0B: aes_sbox_fwd = 8'h2B;
    8'h0C: aes_sbox_fwd = 8'hFE; 8'h0D: aes_sbox_fwd = 8'hD7; 8'h0E: aes_sbox_fwd = 8'hAB; 8'h0F: aes_sbox_fwd = 8'h76; 8'h10: aes_sbox_fwd = 8'hCA; 8'h11: aes_sbox_fwd = 8'h82;
    8'h12: aes_sbox_fwd = 8'hC9; 8'h13: aes_sbox_fwd = 8'h7D; 8'h14: aes_sbox_fwd = 8'hFA; 8'h15: aes_sbox_fwd = 8'h59; 8'h16: aes_sbox_fwd = 8'h47; 8'h17: aes_sbox_fwd = 8'hF0;
    8'h18: aes_sbox_fwd = 8'hAD; 8'h19: aes_sbox_fwd = 8'hD4; 8'h1A: aes_sbox_fwd = 8'hA2; 8'h1B: aes_sbox_fwd = 8'hAF; 8'h1C: aes_sbox_fwd = 8'h9C; 8'h1D: aes_sbox_fwd = 8'hA4;
    8'h1E: aes_sbox_fwd = 8'h72; 8'h1F: aes_sbox_fwd = 8'hC0; 8'h20: aes_sbox_fwd = 8'hB7; 8'h21: aes_sbox_fwd = 8'hFD; 8'h22: aes_sbox_fwd = 8'h93; 8'h23: aes_sbox_fwd = 8'h26;
    8'h24: aes_sbox_fwd = 8'h36; 8'h25: aes_sbox_fwd = 8'h3F; 8'h26: aes_sbox_fwd = 8'hF7; 8'h27: aes_sbox_fwd = 8'hCC; 8'h28: aes_sbox_fwd = 8'h34; 8'h29: aes_sbox_fwd = 8'hA5;
    8'h2A: aes_sbox_fwd = 8'hE5; 8'h2B: aes_sbox_fwd = 8'hF1; 8'h2C: aes_sbox_fwd = 8'h71; 8'h2D: aes_sbox_fwd = 8'hD8; 8'h2E: aes_sbox_fwd = 8'h31; 8'h2F: aes_sbox_fwd = 8'h15;
    8'h30: aes_sbox_fwd = 8'h04; 8'h31: aes_sbox_fwd = 8'hC7; 8'h32: aes_sbox_fwd = 8'h23; 8'h33: aes_sbox_fwd = 8'hC3; 8'h34: aes_sbox_fwd = 8'h18; 8'h35: aes_sbox_fwd = 8'h96;
    8'h36: aes_sbox_fwd = 8'h05; 8'h37: aes_sbox_fwd = 8'h9A; 8'h38: aes_sbox_fwd = 8'h07; 8'h39: aes_sbox_fwd = 8'h12; 8'h3A: aes_sbox_fwd = 8'h80; 8'h3B: aes_sbox_fwd = 8'hE2;
    8'h3C: aes_sbox_fwd = 8'hEB; 8'h3D: aes_sbox_fwd = 8'h27; 8'h3E: aes_sbox_fwd = 8'hB2; 8'h3F: aes_sbox_fwd = 8'h75; 8'h40: aes_sbox_fwd = 8'h09; 8'h41: aes_sbox_fwd = 8'h83;
    8'h42: aes_sbox_fwd = 8'h2C; 8'h43: aes_sbox_fwd = 8'h1A; 8'h44: aes_sbox_fwd = 8'h1B; 8'h45: aes_sbox_fwd = 8'h6E; 8'h46: aes_sbox_fwd = 8'h5A; 8'h47: aes_sbox_fwd = 8'hA0;
    8'h48: aes_sbox_fwd = 8'h52; 8'h49: aes_sbox_fwd = 8'h3B; 8'h4A: aes_sbox_fwd = 8'hD6; 8'h4B: aes_sbox_fwd = 8'hB3; 8'h4C: aes_sbox_fwd = 8'h29; 8'h4D: aes_sbox_fwd = 8'hE3;
    8'h4E: aes_sbox_fwd = 8'h2F; 8'h4F: aes_sbox_fwd = 8'h84; 8'h50: aes_sbox_fwd = 8'h53; 8'h51: aes_sbox_fwd = 8'hD1; 8'h52: aes_sbox_fwd = 8'h00; 8'h53: aes_sbox_fwd = 8'hED;
    8'h54: aes_sbox_fwd = 8'h20; 8'h55: aes_sbox_fwd = 8'hFC; 8'h56: aes_sbox_fwd = 8'hB1; 8'h57: aes_sbox_fwd = 8'h5B; 8'h58: aes_sbox_fwd = 8'h6A; 8'h59: aes_sbox_fwd = 8'hCB;
    8'h5A: aes_sbox_fwd = 8'hBE; 8'h5B: aes_sbox_fwd = 8'h39; 8'h5C: aes_sbox_fwd = 8'h4A; 8'h5D: aes_sbox_fwd = 8'h4C; 8'h5E: aes_sbox_fwd = 8'h58; 8'h5F: aes_sbox_fwd = 8'hCF;
    8'h60: aes_sbox_fwd = 8'hD0; 8'h61: aes_sbox_fwd = 8'hEF; 8'h62: aes_sbox_fwd = 8'hAA; 8'h63: aes_sbox_fwd = 8'hFB; 8'h64: aes_sbox_fwd = 8'h43; 8'h65: aes_sbox_fwd = 8'h4D;
    8'h66: aes_sbox_fwd = 8'h33; 8'h67: aes_sbox_fwd = 8'h85; 8'h68: aes_sbox_fwd = 8'h45; 8'h69: aes_sbox_fwd = 8'hF9; 8'h6A: aes_sbox_fwd = 8'h02; 8'h6B: aes_sbox_fwd = 8'h7F;
    8'h6C: aes_sbox_fwd = 8'h50; 8'h6D: aes_sbox_fwd = 8'h3C; 8'h6E: aes_sbox_fwd = 8'h9F; 8'h6F: aes_sbox_fwd = 8'hA8; 8'h70: aes_sbox_fwd = 8'h51; 8'h71: aes_sbox_fwd = 8'hA3;
    8'h72: aes_sbox_fwd = 8'h40; 8'h73: aes_sbox_fwd = 8'h8F; 8'h74: aes_sbox_fwd = 8'h92; 8'h75: aes_sbox_fwd = 8'h9D; 8'h76: aes_sbox_fwd = 8'h38; 8'h77: aes_sbox_fwd = 8'hF5;
    8'h78: aes_sbox_fwd = 8'hBC; 8'h79: aes_sbox_fwd = 8'hB6; 8'h7A: aes_sbox_fwd = 8'hDA; 8'h7B: aes_sbox_fwd = 8'h21; 8'h7C: aes_sbox_fwd = 8'h10; 8'h7D: aes_sbox_fwd = 8'hFF;
    8'h7E: aes_sbox_fwd = 8'hF3; 8'h7F: aes_sbox_fwd = 8'hD2; 8'h80: aes_sbox_fwd = 8'hCD; 8'h81: aes_sbox_fwd = 8'h0C; 8'h82: aes_sbox_fwd = 8'h13; 8'h83: aes_sbox_fwd = 8'hEC;
    8'h84: aes_sbox_fwd = 8'h5F; 8'h85: aes_sbox_fwd = 8'h97; 8'h86: aes_sbox_fwd = 8'h44; 8'h87: aes_sbox_fwd = 8'h17; 8'h88: aes_sbox_fwd = 8'hC4; 8'h89: aes_sbox_fwd = 8'hA7;
    8'h8A: aes_sbox_fwd = 8'h7E; 8'h8B: aes_sbox_fwd = 8'h3D; 8'h8C: aes_sbox_fwd = 8'h64; 8'h8D: aes_sbox_fwd = 8'h5D; 8'h8E: aes_sbox_fwd = 8'h19; 8'h8F: aes_sbox_fwd = 8'h73;
    8'h90: aes_sbox_fwd = 8'h60; 8'h91: aes_sbox_fwd = 8'h81; 8'h92: aes_sbox_fwd = 8'h4F; 8'h93: aes_sbox_fwd = 8'hDC; 8'h94: aes_sbox_fwd = 8'h22; 8'h95: aes_sbox_fwd = 8'h2A;
    8'h96: aes_sbox_fwd = 8'h90; 8'h97: aes_sbox_fwd = 8'h88; 8'h98: aes_sbox_fwd = 8'h46; 8'h99: aes_sbox_fwd = 8'hEE; 8'h9A: aes_sbox_fwd = 8'hB8; 8'h9B: aes_sbox_fwd = 8'h14;
    8'h9C: aes_sbox_fwd = 8'hDE; 8'h9D: aes_sbox_fwd = 8'h5E; 8'h9E: aes_sbox_fwd = 8'h0B; 8'h9F: aes_sbox_fwd = 8'hDB; 8'hA0: aes_sbox_fwd = 8'hE0; 8'hA1: aes_sbox_fwd = 8'h32;
    8'hA2: aes_sbox_fwd = 8'h3A; 8'hA3: aes_sbox_fwd = 8'h0A; 8'hA4: aes_sbox_fwd = 8'h49; 8'hA5: aes_sbox_fwd = 8'h06; 8'hA6: aes_sbox_fwd = 8'h24; 8'hA7: aes_sbox_fwd = 8'h5C;
    8'hA8: aes_sbox_fwd = 8'hC2; 8'hA9: aes_sbox_fwd = 8'hD3; 8'hAA: aes_sbox_fwd = 8'hAC; 8'hAB: aes_sbox_fwd = 8'h62; 8'hAC: aes_sbox_fwd = 8'h91; 8'hAD: aes_sbox_fwd = 8'h95;
    8'hAE: aes_sbox_fwd = 8'hE4; 8'hAF: aes_sbox_fwd = 8'h79; 8'hB0: aes_sbox_fwd = 8'hE7; 8'hB1: aes_sbox_fwd = 8'hC8; 8'hB2: aes_sbox_fwd = 8'h37; 8'hB3: aes_sbox_fwd = 8'h6D;
    8'hB4: aes_sbox_fwd = 8'h8D; 8'hB5: aes_sbox_fwd = 8'hD5; 8'hB6: aes_sbox_fwd = 8'h4E; 8'hB7: aes_sbox_fwd = 8'hA9; 8'hB8: aes_sbox_fwd = 8'h6C; 8'hB9: aes_sbox_fwd = 8'h56;
    8'hBA: aes_sbox_fwd = 8'hF4; 8'hBB: aes_sbox_fwd = 8'hEA; 8'hBC: aes_sbox_fwd = 8'h65; 8'hBD: aes_sbox_fwd = 8'h7A; 8'hBE: aes_sbox_fwd = 8'hAE; 8'hBF: aes_sbox_fwd = 8'h08;
    8'hC0: aes_sbox_fwd = 8'hBA; 8'hC1: aes_sbox_fwd = 8'h78; 8'hC2: aes_sbox_fwd = 8'h25; 8'hC3: aes_sbox_fwd = 8'h2E; 8'hC4: aes_sbox_fwd = 8'h1C; 8'hC5: aes_sbox_fwd = 8'hA6;
    8'hC6: aes_sbox_fwd = 8'hB4; 8'hC7: aes_sbox_fwd = 8'hC6; 8'hC8: aes_sbox_fwd = 8'hE8; 8'hC9: aes_sbox_fwd = 8'hDD; 8'hCA: aes_sbox_fwd = 8'h74; 8'hCB: aes_sbox_fwd = 8'h1F;
    8'hCC: aes_sbox_fwd = 8'h4B; 8'hCD: aes_sbox_fwd = 8'hBD; 8'hCE: aes_sbox_fwd = 8'h8B; 8'hCF: aes_sbox_fwd = 8'h8A; 8'hD0: aes_sbox_fwd = 8'h70; 8'hD1: aes_sbox_fwd = 8'h3E;
    8'hD2: aes_sbox_fwd = 8'hB5; 8'hD3: aes_sbox_fwd = 8'h66; 8'hD4: aes_sbox_fwd = 8'h48; 8'hD5: aes_sbox_fwd = 8'h03; 8'hD6: aes_sbox_fwd = 8'hF6; 8'hD7: aes_sbox_fwd = 8'h0E;
    8'hD8: aes_sbox_fwd = 8'h61; 8'hD9: aes_sbox_fwd = 8'h35; 8'hDA: aes_sbox_fwd = 8'h57; 8'hDB: aes_sbox_fwd = 8'hB9; 8'hDC: aes_sbox_fwd = 8'h86; 8'hDD: aes_sbox_fwd = 8'hC1;
    8'hDE: aes_sbox_fwd = 8'h1D; 8'hDF: aes_sbox_fwd = 8'h9E; 8'hE0: aes_sbox_fwd = 8'hE1; 8'hE1: aes_sbox_fwd = 8'hF8; 8'hE2: aes_sbox_fwd = 8'h98; 8'hE3: aes_sbox_fwd = 8'h11;
    8'hE4: aes_sbox_fwd = 8'h69; 8'hE5: aes_sbox_fwd = 8'hD9; 8'hE6: aes_sbox_fwd = 8'h8E; 8'hE7: aes_sbox_fwd = 8'h94; 8'hE8: aes_sbox_fwd = 8'h9B; 8'hE9: aes_sbox_fwd = 8'h1E;
    8'hEA: aes_sbox_fwd = 8'h87; 8'hEB: aes_sbox_fwd = 8'hE9; 8'hEC: aes_sbox_fwd = 8'hCE; 8'hED: aes_sbox_fwd = 8'h55; 8'hEE: aes_sbox_fwd = 8'h28; 8'hEF: aes_sbox_fwd = 8'hDF; 8'hF0: aes_sbox_fwd = 8'h8C;
    8'hF1: aes_sbox_fwd = 8'hA1; 8'hF2: aes_sbox_fwd = 8'h89; 8'hF3: aes_sbox_fwd = 8'h0D; 8'hF4: aes_sbox_fwd = 8'hBF; 8'hF5: aes_sbox_fwd = 8'hE6; 8'hF6: aes_sbox_fwd = 8'h42;
    8'hF7: aes_sbox_fwd = 8'h68; 8'hF8: aes_sbox_fwd = 8'h41; 8'hF9: aes_sbox_fwd = 8'h99; 8'hFA: aes_sbox_fwd = 8'h2D; 8'hFB: aes_sbox_fwd = 8'h0F; 8'hFC: aes_sbox_fwd = 8'hB0;
    8'hFD: aes_sbox_fwd = 8'h54; 8'hFE: aes_sbox_fwd = 8'hBB; 8'hFF: aes_sbox_fwd = 8'h16;
    default: aes_sbox_fwd = 8'h00;
    endcase
    endfunction
    genvar i, m, n, q;
    for (i = 0; i < (CVA6Cfg.XLEN / 8); i++) begin : brev8_xperm8_gen
      // Generating xperm8_result by extracting bytes from operand a based on indices from operand b
      assign xperm8_result[i << 3 +: 8] = (fu_data_i.operand_b[i << 3 +: 8] < (CVA6Cfg.XLEN / 8)) ? fu_data_i.operand_a[fu_data_i.operand_b[i << 3 +: 8] << 3 +: 8] : 8'b0;
      // Generate brev8_reversed by reversing bits within each byte
      for (m = 0; m < 8; m++) begin : reverse_bits
        // Reversing the order of bits within a single byte
        assign brev8_reversed[(i<<3)+m] = fu_data_i.operand_a[(i<<3)+(7-m)];
      end
    end
    for (q = 0; q < (CVA6Cfg.XLEN / 4); q++) begin : xperm4_gen
      // Generating xperm4_result by extracting nibbles from operand a based on indices from operand b
      assign xperm4_result[q << 2 +: 4] = (fu_data_i.operand_b[q << 2 +: 4] < (CVA6Cfg.XLEN / 4)) ? fu_data_i.operand_a[{2'b0, fu_data_i.operand_b[q << 2 +: 4]} << 2 +: 4] : 4'b0;
    end
    if (CVA6Cfg.IS_XLEN32) begin
      // Generate zip and unzip results
      for (n = 0; n < 16; n++) begin : zip_unzip_gen
        // Assigning lower and upper half of operand into the even and odd positions of result
        assign zip_gen[n<<1] = fu_data_i.operand_a[n];
        assign zip_gen[(n<<1)+1] = fu_data_i.operand_a[n+16];
        // Assigning even and odd bits of operand into lower and upper halves of result
        assign unzip_gen[n] = fu_data_i.operand_a[n<<1];
        assign unzip_gen[n+16] = fu_data_i.operand_a[(n<<1)+1];
      end
      // AES encryption results
      //assign sbox_in = (fu_data_i.operand_b >> {bs, 3'b000}) & 8'hFF;
      //assign sbox_out = aes_sbox_fwd(sbox_in);
      //assign aes32esi_gen = fu_data_i.operand_a ^ (({24'b0, sbox_out} << {bs, 3'b000}) | ({24'b0, sbox_out} >> (32 - {bs, 3'b000})));
      //assign mix_out = aes_mixcolumn_fwd(aes32esi_gen);
      //assign aes32esmi_gen = fu_data_i.operand_a ^ ((mix_out << {bs, 3'b000}) | (mix_out >> (32 - {bs, 3'b000})));
    end
    else if (CVA6Cfg.IS_XLEN64) begin
      // Shift rows step
      assign sr = {fu_data_i.operand_a[31:24], fu_data_i.operand_b[55:48], fu_data_i.operand_b[15:8], fu_data_i.operand_a[39:32], fu_data_i.operand_b[63:56], fu_data_i.operand_b[23:16], fu_data_i.operand_a[47:40], fu_data_i.operand_a[7:0]};
      assign aes64es_gen = {aes_sbox_fwd(sr[63:56]), aes_sbox_fwd(sr[55:48]), aes_sbox_fwd(sr[47:40]), aes_sbox_fwd(sr[39:32]), aes_sbox_fwd(sr[31:24]), aes_sbox_fwd(sr[23:16]), aes_sbox_fwd(sr[15:8]),  aes_sbox_fwd(sr[7:0])};
      assign aes64esm_gen = {aes_mixcolumn_fwd(aes64es_gen[63:32]), aes_mixcolumn_fwd(aes64es_gen[31:0])};
      assign aes64ks2_gen = {(fu_data_i.operand_a[63:32] ^ fu_data_i.operand_b[31:0] ^ fu_data_i.operand_b[63:32]), (fu_data_i.operand_a[63:32] ^ fu_data_i.operand_b[31:0])};
      //assign aes64ks1i_gen = bring inst bits here too
    end
  end

  // -----------
  // Result MUX
  // -----------
  always_comb begin
    result_o = '0;
    if (CVA6Cfg.IS_XLEN64) begin
      unique case (fu_data_i.operation)
        // Add word: Ignore the upper bits and sign extend to 64 bit
        ADDW, SUBW: result_o = {{CVA6Cfg.XLEN - 32{adder_result[31]}}, adder_result[31:0]};
        SH1ADDUW, SH2ADDUW, SH3ADDUW: result_o = adder_result;
        // Shifts 32 bit
        SLLW, SRLW, SRAW:
        result_o = {{CVA6Cfg.XLEN - 32{shift_result32[31]}}, shift_result32[31:0]};
        default: ;
      endcase
    end
    unique case (fu_data_i.operation)
      // Standard Operations
      ANDL, ANDN: result_o = fu_data_i.operand_a & operand_b_neg[CVA6Cfg.XLEN:1];
      ORL, ORN: result_o = fu_data_i.operand_a | operand_b_neg[CVA6Cfg.XLEN:1];
      XORL, XNOR: result_o = fu_data_i.operand_a ^ operand_b_neg[CVA6Cfg.XLEN:1];
      // Adder Operations
      ADD, SUB, ADDUW, SH1ADD, SH2ADD, SH3ADD: result_o = adder_result;
      // Shift Operations
      SLL, SRL, SRA: result_o = (CVA6Cfg.IS_XLEN64) ? shift_result : shift_result32;
      // Comparison Operations
      SLTS, SLTU: result_o = {{CVA6Cfg.XLEN - 1{1'b0}}, less};
      default: ;  // default case to suppress unique warning
    endcase

    if (CVA6Cfg.RVB) begin
      // Index for Bitwise Rotation
      bit_indx = 1 << (fu_data_i.operand_b & (CVA6Cfg.XLEN - 1));
      if (CVA6Cfg.IS_XLEN64) begin
        // rolw, roriw, rorw
        rolw = ({{CVA6Cfg.XLEN-32{1'b0}},fu_data_i.operand_a[31:0]} << fu_data_i.operand_b[4:0]) | ({{CVA6Cfg.XLEN-32{1'b0}},fu_data_i.operand_a[31:0]} >> (CVA6Cfg.XLEN-32-fu_data_i.operand_b[4:0]));
        rorw = ({{CVA6Cfg.XLEN-32{1'b0}},fu_data_i.operand_a[31:0]} >> fu_data_i.operand_b[4:0]) | ({{CVA6Cfg.XLEN-32{1'b0}},fu_data_i.operand_a[31:0]} << (CVA6Cfg.XLEN-32-fu_data_i.operand_b[4:0]));
        unique case (fu_data_i.operation)
          CLZW, CTZW:
          result_o = (lz_tz_wempty) ? 32 : {{CVA6Cfg.XLEN - 5{1'b0}}, lz_tz_wcount};  // change
          ROLW: result_o = {{CVA6Cfg.XLEN - 32{rolw[31]}}, rolw};
          RORW, RORIW: result_o = {{CVA6Cfg.XLEN - 32{rorw[31]}}, rorw};
          default: ;
        endcase
      end
      unique case (fu_data_i.operation)
        // Integer minimum/maximum
        MAX:  result_o = less ? fu_data_i.operand_b : fu_data_i.operand_a;
        MAXU: result_o = less ? fu_data_i.operand_b : fu_data_i.operand_a;
        MIN:  result_o = ~less ? fu_data_i.operand_b : fu_data_i.operand_a;
        MINU: result_o = ~less ? fu_data_i.operand_b : fu_data_i.operand_a;

        // Single bit instructions operations
        BCLR, BCLRI: result_o = fu_data_i.operand_a & ~bit_indx;
        BEXT, BEXTI: result_o = {{CVA6Cfg.XLEN - 1{1'b0}}, |(fu_data_i.operand_a & bit_indx)};
        BINV, BINVI: result_o = fu_data_i.operand_a ^ bit_indx;
        BSET, BSETI: result_o = fu_data_i.operand_a | bit_indx;

        // Count Leading/Trailing Zeros
        CLZ, CTZ:
        result_o = (lz_tz_empty) ? ({{CVA6Cfg.XLEN - $clog2(CVA6Cfg.XLEN) {1'b0}}, lz_tz_count} + 1)
            : {{CVA6Cfg.XLEN - $clog2(CVA6Cfg.XLEN) {1'b0}}, lz_tz_count};

        // Count population
        CPOP, CPOPW: result_o = {{(CVA6Cfg.XLEN - ($clog2(CVA6Cfg.XLEN) + 1)) {1'b0}}, cpop};

        // Sign and Zero Extend
        SEXTB: result_o = {{CVA6Cfg.XLEN - 8{fu_data_i.operand_a[7]}}, fu_data_i.operand_a[7:0]};
        SEXTH: result_o = {{CVA6Cfg.XLEN - 16{fu_data_i.operand_a[15]}}, fu_data_i.operand_a[15:0]};
        ZEXTH: result_o = {{CVA6Cfg.XLEN - 16{1'b0}}, fu_data_i.operand_a[15:0]};

        // Bitwise Rotation
        ROL:
        result_o = (CVA6Cfg.IS_XLEN64) ? ((fu_data_i.operand_a << fu_data_i.operand_b[5:0]) | (fu_data_i.operand_a >> (CVA6Cfg.XLEN-fu_data_i.operand_b[5:0]))) : ((fu_data_i.operand_a << fu_data_i.operand_b[4:0]) | (fu_data_i.operand_a >> (CVA6Cfg.XLEN-fu_data_i.operand_b[4:0])));

        ROR, RORI:
        result_o = (CVA6Cfg.IS_XLEN64) ? ((fu_data_i.operand_a >> fu_data_i.operand_b[5:0]) | (fu_data_i.operand_a << (CVA6Cfg.XLEN-fu_data_i.operand_b[5:0]))) : ((fu_data_i.operand_a >> fu_data_i.operand_b[4:0]) | (fu_data_i.operand_a << (CVA6Cfg.XLEN-fu_data_i.operand_b[4:0])));

        ORCB: result_o = orcbw_result;
        REV8: result_o = rev8w_result;

        default:
        if (fu_data_i.operation == SLLIUW && CVA6Cfg.IS_XLEN64)
          result_o = {{CVA6Cfg.XLEN-32{1'b0}}, fu_data_i.operand_a[31:0]} << fu_data_i.operand_b[5:0];  // Left Shift 32 bit unsigned
      endcase
    end
    if (CVA6Cfg.RVZiCond) begin
      unique case (fu_data_i.operation)
        CZERO_EQZ:
        result_o = (|fu_data_i.operand_b) ? fu_data_i.operand_a : '0;  // move zero to rd if rs2 is equal to zero else rs1
        CZERO_NEZ:
        result_o = (|fu_data_i.operand_b) ? '0 : fu_data_i.operand_a; // move zero to rd if rs2 is nonzero else rs1
        default: ;  // default case to suppress unique warning
      endcase
    end
    // ZKN instructions
    if (CVA6Cfg.ZKN && CVA6Cfg.RVB) begin
      unique case (fu_data_i.operation)
        PACK:
        result_o = (CVA6Cfg.IS_XLEN32) ? ({fu_data_i.operand_b[15:0], fu_data_i.operand_a[15:0]}) : ({fu_data_i.operand_b[31:0], fu_data_i.operand_a[31:0]});
        PACK_H:
        result_o = (CVA6Cfg.IS_XLEN32) ? ({16'b0, fu_data_i.operand_b[7:0], fu_data_i.operand_a[7:0]}) : ({48'b0, fu_data_i.operand_b[7:0], fu_data_i.operand_a[7:0]});
        BREV8: result_o = brev8_reversed;
        XPERM8: result_o = xperm8_result;
        XPERM4: result_o = xperm4_result;
        default: ;
      endcase
      if (fu_data_i.operation == PACK_W && CVA6Cfg.IS_XLEN64)
        result_o = {
          {32{fu_data_i.operand_b[15]}}, {fu_data_i.operand_b[15:0]}, {fu_data_i.operand_a[15:0]}
        };
      if (fu_data_i.operation == UNZIP && CVA6Cfg.IS_XLEN32) result_o = unzip_gen;
      if (fu_data_i.operation == ZIP && CVA6Cfg.IS_XLEN32) result_o = zip_gen;
      //if (fu_data_i.operation == AES32ESI && CVA6Cfg.IS_XLEN32) result_o = aes32esi_gen;
      //if (fu_data_i.operation == AES32ESMI && CVA6Cfg.IS_XLEN32) result_o = aes32esmi_gen;
      if (fu_data_i.operation == AES64ES && CVA6Cfg.IS_XLEN64) result_o = aes64es_gen;
      if (fu_data_i.operation == AES64ESM && CVA6Cfg.IS_XLEN64) result_o = aes64esm_gen;
      //if (fu_data_i.operation == AES64KS1I && CVA6Cfg.IS_XLEN64) result_o = aes64ks1i_gen;
      if (fu_data_i.operation == AES64KS2 && CVA6Cfg.IS_XLEN64) result_o = aes64ks2_gen;
    end
  end
endmodule
