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


module alu import ariane_pkg::*;(
    input  logic                     clk_i,          // Clock
    input  logic                     rst_ni,         // Asynchronous reset active low
    input  fu_data_t                 fu_data_i,
    output riscv::xlen_t             result_o,
    output logic                     alu_branch_res_o
);

    riscv::xlen_t operand_a_rev;
    logic [31:0] operand_a_rev32;
    logic [riscv::XLEN:0] operand_b_neg;
    logic [riscv::XLEN+1:0] adder_result_ext_o;
    logic        less;  // handles both signed and unsigned forms
    logic [31:0] rolw;                    // Rotate Left Word
    logic [31:0] rorw;                    // Rotate Right Word
    logic [$clog2(riscv::XLEN)-1:0] cpop; // Count Population
    logic [riscv::XLEN-1:0] src_operand;  // Count Leading/Trailing Zeros operand_a
    logic [5:0] lzcount;                  // Count Leading Zeros
    logic [4:0] lzwcount;                 // Count Leading Zeros Word
    logic [5:0] tzcount;                  // Count Trailing Zeros
    logic [4:0] tzwcount;                 // Count Trailing Zeros Word

    // bit reverse operand_a for left shifts and bit counting
    generate
      genvar k;
      for(k = 0; k < riscv::XLEN; k++)
        assign operand_a_rev[k] = fu_data_i.operand_a[riscv::XLEN-1-k];

      for (k = 0; k < 32; k++)
        assign operand_a_rev32[k] = fu_data_i.operand_a[31-k];
    endgenerate

    // ------
    // Adder
    // ------
    logic        adder_op_b_negate;
    logic        adder_z_flag;
    logic [riscv::XLEN:0] adder_in_a, adder_in_b;
    riscv::xlen_t adder_result;

    always_comb begin
      adder_op_b_negate = 1'b0;

      unique case (fu_data_i.operator)
        // ADDER OPS
        EQ,  NE,
        SUB, SUBW: adder_op_b_negate = 1'b1;

        default: ;
      endcase
    end

    // prepare operand a
    assign adder_in_a    = {fu_data_i.operand_a, 1'b1};

    // prepare operand b
    assign operand_b_neg = {fu_data_i.operand_b, 1'b0} ^ {riscv::XLEN+1{adder_op_b_negate}};
    assign adder_in_b    =  operand_b_neg ;

    // actual adder
    assign adder_result_ext_o = $unsigned(adder_in_a) + $unsigned(adder_in_b);
    assign adder_result       = adder_result_ext_o[riscv::XLEN:1];
    assign adder_z_flag       = ~|adder_result;

    // get the right branch comparison result
    always_comb begin : branch_resolve
        // set comparison by default
        alu_branch_res_o      = 1'b1;
        case (fu_data_i.operator)
            EQ:       alu_branch_res_o = adder_z_flag;
            NE:       alu_branch_res_o = ~adder_z_flag;
            LTS, LTU: alu_branch_res_o = less;
            GES, GEU: alu_branch_res_o = ~less;
            default:  alu_branch_res_o = 1'b1;
        endcase
    end

    // ---------
    // Shifts
    // ---------

    // TODO: this can probably optimized significantly
    logic        shift_left;          // should we shift left
    logic        shift_arithmetic;

    riscv::xlen_t shift_amt;           // amount of shift, to the right
    riscv::xlen_t shift_op_a;          // input of the shifter
    logic [31:0] shift_op_a32;        // input to the 32 bit shift operation

    riscv::xlen_t shift_result;
    logic [31:0] shift_result32;

    logic [riscv::XLEN:0] shift_right_result;
    logic [32:0] shift_right_result32;

    riscv::xlen_t shift_left_result;
    logic [31:0] shift_left_result32;

    assign shift_amt = fu_data_i.operand_b;

    assign shift_left = (fu_data_i.operator == SLL) | (fu_data_i.operator == SLLW);

    assign shift_arithmetic = (fu_data_i.operator == SRA) | (fu_data_i.operator == SRAW);

    // right shifts, we let the synthesizer optimize this
    logic [riscv::XLEN:0] shift_op_a_64;
    logic [32:0] shift_op_a_32;

    // choose the bit reversed or the normal input for shift operand a
    assign shift_op_a    = shift_left ? operand_a_rev   : fu_data_i.operand_a;
    assign shift_op_a32  = shift_left ? operand_a_rev32 : fu_data_i.operand_a[31:0];

    assign shift_op_a_64 = { shift_arithmetic & shift_op_a[riscv::XLEN-1], shift_op_a};
    assign shift_op_a_32 = { shift_arithmetic & shift_op_a[31], shift_op_a32};

    assign shift_right_result     = $unsigned($signed(shift_op_a_64) >>> shift_amt[5:0]);

    assign shift_right_result32   = $unsigned($signed(shift_op_a_32) >>> shift_amt[4:0]);
    // bit reverse the shift_right_result for left shifts
    genvar j;
    generate
      for(j = 0; j < riscv::XLEN; j++)
        assign shift_left_result[j] = shift_right_result[riscv::XLEN-1-j];

      for(j = 0; j < 32; j++)
        assign shift_left_result32[j] = shift_right_result32[31-j];

    endgenerate

    assign shift_result = shift_left ? shift_left_result : shift_right_result[riscv::XLEN-1:0];
    assign shift_result32 = shift_left ? shift_left_result32 : shift_right_result32[31:0];

    // ------------
    // Comparisons
    // ------------

    always_comb begin
        logic sgn;
        sgn = 1'b0;

        if ((fu_data_i.operator == SLTS) ||
            (fu_data_i.operator == LTS)  ||
            (fu_data_i.operator == GES))
            sgn = 1'b1;

        less = ($signed({sgn & fu_data_i.operand_a[riscv::XLEN-1], fu_data_i.operand_a})  <  $signed({sgn & fu_data_i.operand_b[riscv::XLEN-1], fu_data_i.operand_b}));
    end

    if (ariane_pkg::BITMANIP) begin : gen_bitmanip
        // Bitwise Rotation

        // rolw, roriw, rorw
        always_comb begin
          rolw = ({{32{1'b0}},fu_data_i.operand_a[31:0]} << fu_data_i.operand_b[4:0]) | ({{32{1'b0}},fu_data_i.operand_a[31:0]} >> (riscv::XLEN-32-fu_data_i.operand_b[4:0]));
          rorw = ({{32{1'b0}},fu_data_i.operand_a[31:0]} >> fu_data_i.operand_b[4:0]) | ({{32{1'b0}},fu_data_i.operand_a[31:0]} << (riscv::XLEN-32-fu_data_i.operand_b[4:0]));
        end

        // Count Population + Count population Word
        assign src_operand = (fu_data_i.operator == CPOPW) ? fu_data_i.operand_a[31:0] : fu_data_i.operand_a[63:0];
        popcount i_cpop_count (
          .data_i           (src_operand),
          .popcount_o       (cpop)
        );

        // Count Leading/Trailing Zeros

        // Count Leading Zeros
        lzc #(
          .WIDTH(64),
          .MODE (1)
        ) i_clz_64b (
          .in_i (fu_data_i.operand_a),
          .cnt_o (lzcount),
          .empty_o ()
        );

        // Count Leading Zeros Word
        lzc #(
          .WIDTH(32),
          .MODE (1)
        ) i_clz_32b (
          .in_i (fu_data_i.operand_a),
          .cnt_o (lzwcount),
          .empty_o ()
        );

        // Count Trailing Zeros
        lzc #(
          .WIDTH(64),
          .MODE (0)
        ) i_ctz_64b (
          .in_i (fu_data_i.operand_a),
          .cnt_o (tzcount),
          .empty_o ()
        );

        // Count Trailing Zeros Word
        lzc #(
          .WIDTH(32),
          .MODE (0)
        ) i_ctz_32b (
          .in_i (fu_data_i.operand_a),
          .cnt_o (tzwcount),
          .empty_o ()
        );
    end

    // -----------
    // Result MUX
    // -----------
    always_comb begin
        result_o   = '0;
        unique case (fu_data_i.operator)
            // Standard Operations
            ANDL:  result_o = fu_data_i.operand_a & fu_data_i.operand_b;
            ORL:   result_o = fu_data_i.operand_a | fu_data_i.operand_b;
            XORL:  result_o = fu_data_i.operand_a ^ fu_data_i.operand_b;

            // Adder Operations
            ADD, SUB: result_o = adder_result;
            // Add word: Ignore the upper bits and sign extend to 64 bit
            ADDW, SUBW: result_o = {{riscv::XLEN-32{adder_result[31]}}, adder_result[31:0]};
            // Shift Operations
            SLL,
            SRL, SRA: result_o = (riscv::XLEN == 64) ? shift_result : shift_result32;
            // Shifts 32 bit
            SLLW,
            SRLW, SRAW: result_o = {{riscv::XLEN-32{shift_result32[31]}}, shift_result32[31:0]};

            // Comparison Operations
            SLTS,  SLTU: result_o = {{riscv::XLEN-1{1'b0}}, less};

            default: ; // default case to suppress unique warning
        endcase
        if (ariane_pkg::BITMANIP) begin
            unique case (fu_data_i.operator)
                // Bitmanip Logical with Negate operations
                ANDN: result_o = fu_data_i.operand_a & ~fu_data_i.operand_b;
                ORN:  result_o = fu_data_i.operand_a | ~fu_data_i.operand_b;
                XNOR: result_o = ~(fu_data_i.operand_a ^ fu_data_i.operand_b);

                // Bitmanip Shift with Add operations
                SH1ADD: result_o = (fu_data_i.operand_a << 1) + fu_data_i.operand_b;
                SH2ADD: result_o = (fu_data_i.operand_a << 2) + fu_data_i.operand_b;
                SH3ADD: result_o = (fu_data_i.operand_a << 3) + fu_data_i.operand_b;

                // Bitmanip Shift with Add operations (Unsigned Word)
                SH1ADDUW: result_o = ({{32{1'b0}}, fu_data_i.operand_a[31:0]} << 1) + fu_data_i.operand_b;
                SH2ADDUW: result_o = ({{32{1'b0}}, fu_data_i.operand_a[31:0]} << 2) + fu_data_i.operand_b;
                SH3ADDUW: result_o = ({{32{1'b0}}, fu_data_i.operand_a[31:0]} << 3) + fu_data_i.operand_b;

                // Unsigned word operations
                ADDUW:  result_o = ({{32{1'b0}}, fu_data_i.operand_a[31:0]}) + fu_data_i.operand_b;
                SLLIUW: result_o = ({{32{1'b0}}, fu_data_i.operand_a[31:0]} << fu_data_i.operand_b[5:0]);

                // Integer minimum/maximum
                MAX:  result_o = ($signed(fu_data_i.operand_a) < $signed(fu_data_i.operand_b)) ? fu_data_i.operand_b : fu_data_i.operand_a;
                MAXU: result_o = ($unsigned(fu_data_i.operand_a) < $unsigned(fu_data_i.operand_b)) ? fu_data_i.operand_b : fu_data_i.operand_a;
                MIN:  result_o = ($signed(fu_data_i.operand_a) > $signed(fu_data_i.operand_b)) ? fu_data_i.operand_b : fu_data_i.operand_a;
                MINU: result_o = ($unsigned(fu_data_i.operand_a) > $unsigned(fu_data_i.operand_b)) ? fu_data_i.operand_b : fu_data_i.operand_a;

                // Single bit instructions operations
                BCLR, BCLRI: result_o = fu_data_i.operand_a & ~(1 << (fu_data_i.operand_b & (riscv::XLEN-1)));
                BEXT, BEXTI: result_o = (fu_data_i.operand_a >> (fu_data_i.operand_b & (riscv::XLEN-1))) & 1;
                BINV, BINVI: result_o = fu_data_i.operand_a ^ (1 << (fu_data_i.operand_b & (riscv::XLEN-1)));
                BSET, BSETI: result_o = fu_data_i.operand_a | (1 << (fu_data_i.operand_b & (riscv::XLEN-1)));

                // Count Leading/Trailing Zeros
                CLZ:   result_o = ~(|fu_data_i.operand_a) ? 64 : lzcount;
                CLZW:  result_o = ~(|fu_data_i.operand_a[31:0]) ? 32 : lzwcount;
                CTZ:   result_o = ~(|fu_data_i.operand_a) ? 64 : tzcount;
                CTZW:  result_o = ~(|fu_data_i.operand_a[31:0]) ? 32 : tzwcount;

                // Count population
                CPOP, CPOPW: result_o = cpop;

                // Sign and Zero Extend
                SEXTB: result_o = {{riscv::XLEN-8{fu_data_i.operand_a[7]}}, fu_data_i.operand_a[7:0]};
                SEXTH: result_o = {{riscv::XLEN-8{fu_data_i.operand_a[15]}}, fu_data_i.operand_a[15:0]};
                ZEXTH: result_o = {{riscv::XLEN-8{1'b0}}, fu_data_i.operand_a[15:0]};

                // Bitwise Rotation
                ROL:          result_o = (fu_data_i.operand_a << fu_data_i.operand_b[5:0]) | (fu_data_i.operand_a >> (riscv::XLEN-fu_data_i.operand_b[5:0]));
                ROLW:         result_o = {{riscv::XLEN-32{rolw[31]}}, rolw};
                ROR, RORI:    result_o = (fu_data_i.operand_a >> fu_data_i.operand_b[5:0]) | (fu_data_i.operand_a << (riscv::XLEN-fu_data_i.operand_b[5:0]));
                RORW, RORIW:  result_o = {{riscv::XLEN-32{rorw[31]}}, rorw};
                ORCB:         result_o = {{8{|fu_data_i.operand_a[63:56]}}, {8{|fu_data_i.operand_a[55:48]}}, {8{|fu_data_i.operand_a[47:40]}}, {8{|fu_data_i.operand_a[39:32]}}, {8{|fu_data_i.operand_a[31:24]}}, {8{|fu_data_i.operand_a[23:16]}}, {8{|fu_data_i.operand_a[15:8]}}, {8{|fu_data_i.operand_a[7:0]}}};
                REV8:         result_o = {{fu_data_i.operand_a[7:0]}, {fu_data_i.operand_a[15:8]}, {fu_data_i.operand_a[23:16]}, {fu_data_i.operand_a[31:24]}, {fu_data_i.operand_a[39:32]}, {fu_data_i.operand_a[47:40]}, {fu_data_i.operand_a[55:48]}, {fu_data_i.operand_a[63:56]}};

                default: ; // default case to suppress unique warning
            endcase
        end
    end
endmodule
