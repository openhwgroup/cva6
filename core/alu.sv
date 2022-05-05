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

`ifdef BITMANIP
    logic [riscv::XLEN-1:0] cpop;  // Count Population
    logic [riscv::XLEN-1:0] cpopw; // Count Population Word
    logic [riscv::XLEN-33:0] rolw; // Rotate Left Word
    logic [riscv::XLEN-33:0] rorw; // Rotate Right Word

    // ctz variables
    logic [riscv::XLEN-1:0] ctz;   // Count Trailing Zeros
    logic [31:0] tmp32;
    logic [15:0] tmp16;
    logic [7:0] tmp8;
    logic [3:0] tmp4;
    logic [1:0] tmp2;

    // clz variables
    logic [riscv::XLEN-1:0] clz;   // Count Leading Zeros
    logic [31:0] temp32;
    logic [15:0] temp16;
    logic [7:0] temp8;
    logic [3:0] temp4;
    logic [1:0] temp2;

    // clzw variables
    logic [riscv::XLEN-1:0] clzw;  // Count Leading Zeros Word
    logic [15:0] tem16;
    logic [7:0] tem8;
    logic [3:0] tem4;
    logic [1:0] tem2;

    // ctzw variables
    logic [riscv::XLEN-1:0] ctzw;  // Count Training Zeros Word
    logic [15:0] tm16;
    logic [7:0] tm8;
    logic [3:0] tm4;
    logic [1:0] tm2;
`endif

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
`ifdef BITMANIP
    // Count Leading/Trailing Zeros
    integer a;

    // Count Leading Zeros (clz)
    always @ * begin
      clz = 0;
      if(~(|fu_data_i.operand_a[63:32])) begin
        temp32 = fu_data_i.operand_a[31:0];
        clz += 32;
      end
      else 
        temp32 = fu_data_i.operand_a[63:32];
      if(~(|temp32[31:16])) begin
        temp16 = temp32[15:0];
        clz += 16;
      end
      else 
        temp16 = temp32[31:16];
      if(~(|temp16[15:8])) begin
        temp8 = temp16[7:0];
        clz += 8;
      end
      else 
        temp8 = temp16[15:8];
      if(~(|temp8[7:4])) begin
        temp4 = temp8[3:0];
        clz += 4;
      end
      else 
        temp4 = temp8[7:4];
      if(~(|temp4[3:2])) begin
        temp2 = temp4[1:0];
        clz += 2;
      end
      else
        temp2 = temp4[3:2];
      if(~temp2[1]) begin
        clz += 1;
        if(~temp2[0]) begin
          clz += 1;
        end
        else 		
          clz += 0;
      end
      else 		
        clz += 0;
    end

    // Count Trailing Zeros (ctz)
    always @ * begin
      ctz = 64;
      if(~(|fu_data_i.operand_a[31:0])) begin
        tmp32 = fu_data_i.operand_a[63:32];
      end
      else begin
        tmp32 = fu_data_i.operand_a[31:0];
        ctz -= 32;
      end
      if(~(|tmp32[15:0])) begin
        tmp16 = tmp32[31:16];
      end
      else begin
        tmp16 = tmp32[15:0];
        ctz -= 16;
      end
      if(~(|tmp16[7:0])) begin
        tmp8 = tmp16[15:8];
      end
      else begin
        tmp8 = tmp16[7:0];
        ctz -= 8;
      end
      if(~(|tmp8[3:0])) begin
        tmp4 = tmp8[7:4];
      end
      else begin
        tmp4 = tmp8[3:0];
        ctz -= 4;
      end
      if(~(|tmp4[1:0])) begin
        tmp2 = tmp4[3:2];
      end
      else begin
        tmp2 = tmp4[1:0];
        ctz -= 2;
      end
      if(~tmp2[0]) begin
        if(~tmp2[1]) begin
          ctz -= 0;
        end
        else 		
          ctz -= 1;
      end
      else begin
        ctz -= 2;
      end
    end

    // Count Leading Zeros Word (clzw)
    always @ * begin
      clzw = 0;
      if(~(|fu_data_i.operand_a[31:16])) begin
        tem16 = fu_data_i.operand_a[15:0];
        clzw += 16;
      end
      else 
        tem16 = fu_data_i.operand_a[31:16];
      if(~(|tem16[15:8])) begin
        tem8 = tem16[7:0];
        clzw += 8;
      end
      else 
        tem8 = tem16[15:8];
      if(~(|tem8[7:4])) begin
        tem4 = tem8[3:0];
        clzw += 4;
      end
      else 
        tem4 = tem8[7:4];
      if(~(|tem4[3:2])) begin
        tem2 = tem4[1:0];
        clzw += 2;
      end
      else 
        tem2 = tem4[3:2];
      if(~tem2[1]) begin
        clzw += 1;
        if(~tem2[0]) begin
          clzw += 1;
        end
        else 		
          clzw += 0;
      end
      else
        clzw += 0;
    end

    // Count Trailing Zeros Word (ctzw)
    always @ * begin
      ctzw = 32;
      if(~(|fu_data_i.operand_a[15:0])) begin
        tm16 = fu_data_i.operand_a[31:16];
      end
      else begin
        tm16 = fu_data_i.operand_a[15:0];
        ctzw -= 16;
      end
      if(~(|tm16[7:0])) begin
        tm8 = tm16[15:8];
      end
      else begin
        tm8 = tm16[7:0];
        ctzw -= 8;
      end
      if(~(|tm8[3:0])) begin
        tm4 = tm8[7:4];
      end
      else begin
        tm4 = tm8[3:0];
        ctzw -= 4;
      end
      if(~(|tm4[1:0])) begin
        tm2 = tm4[3:2];
      end
      else begin
        tm2 = tm4[1:0];
        ctzw -= 2;
      end
      if(~tm2[0]) begin
        if(~tm2[1]) begin
          ctzw -= 0;
        end
        else 		
          ctzw -= 1;
      end
      else 		
        ctzw -= 2;
    end

    // Count Population
    // cpop, cpopw
    integer c;
    always@ * begin
      cpop = 0;
      c = (fu_data_i.operator == CPOP) ? 64 : 32; 
      for (a=0; a<c; a++) begin
        cpop += fu_data_i.operand_a[a];
      end
    end
    // Bitwise Rotation
    // rolw, roriw, rorw
    always @* begin
      rolw = ({{32{1'b0}},fu_data_i.operand_a[31:0]} << fu_data_i.operand_b[4:0]) | ({{32{1'b0}},fu_data_i.operand_a[31:0]} >> (riscv::XLEN-32-fu_data_i.operand_b[4:0]));
      rorw = ({{32{1'b0}},fu_data_i.operand_a[31:0]} >> fu_data_i.operand_b[4:0]) | ({{32{1'b0}},fu_data_i.operand_a[31:0]} << (riscv::XLEN-32-fu_data_i.operand_b[4:0]));
    end
`endif

    // -----------
    // Result MUX
    // -----------
    always_comb begin
        result_o   = '0;
`ifndef BITMANIP
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
`else
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

            // Count Leading/Training Zeros
            CLZ:  result_o = clz;
            CLZW: result_o = clzw;
            CTZ:  result_o = ctz;
            CTZW: result_o = ctzw;

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
`endif
    end
endmodule
