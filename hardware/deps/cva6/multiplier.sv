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
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
//
// Description: Multiplication Unit with one pipeline register
//              This unit relies on retiming features of the synthesizer
//


module multiplier import ariane_pkg::*; (
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,
    input  logic                     mult_valid_i,
    input  fu_op                     operator_i,
    input  riscv::xlen_t             operand_a_i,
    input  riscv::xlen_t             operand_b_i,
    output riscv::xlen_t             result_o,
    output logic                     mult_valid_o,
    output logic                     mult_ready_o,
    output logic [TRANS_ID_BITS-1:0] mult_trans_id_o
);
    // Pipeline register
    logic [TRANS_ID_BITS-1:0]    trans_id_q;
    logic                        mult_valid_q;
    fu_op                        operator_d, operator_q;
    logic [riscv::XLEN*2-1:0] mult_result_d, mult_result_q;

    // control registers
    logic                       sign_a, sign_b;
    logic                       mult_valid;

    // control signals
    assign mult_valid_o    = mult_valid_q;
    assign mult_trans_id_o = trans_id_q;
    assign mult_ready_o    = 1'b1;

    assign mult_valid      = mult_valid_i && (operator_i inside {MUL, MULH, MULHU, MULHSU, MULW});
    // datapath
    logic [riscv::XLEN*2-1:0] mult_result;
    assign mult_result   = $signed({operand_a_i[riscv::XLEN-1] & sign_a, operand_a_i}) * $signed({operand_b_i[riscv::XLEN-1] & sign_b, operand_b_i});

    // Sign Select MUX
    always_comb begin
        sign_a = 1'b0;
        sign_b = 1'b0;

        // signed multiplication
        if (operator_i == MULH) begin
            sign_a   = 1'b1;
            sign_b   = 1'b1;
        // signed - unsigned multiplication
        end else if (operator_i == MULHSU) begin
            sign_a   = 1'b1;
        // unsigned multiplication
        end else begin
            sign_a   = 1'b0;
            sign_b   = 1'b0;
        end
    end


    // single stage version
    assign mult_result_d   = $signed({operand_a_i[riscv::XLEN-1] & sign_a, operand_a_i}) *
                             $signed({operand_b_i[riscv::XLEN-1] & sign_b, operand_b_i});


    assign operator_d = operator_i;
    always_comb begin : p_selmux
        unique case (operator_q)
            MULH, MULHU, MULHSU: result_o = mult_result_q[riscv::XLEN*2-1:riscv::XLEN];
            MULW:                result_o = sext32(mult_result_q[31:0]);
            // MUL performs an XLEN-bit×XLEN-bit multiplication and places the lower XLEN bits in the destination register
            default:             result_o = mult_result_q[riscv::XLEN-1:0];// including MUL
        endcase
    end

    // -----------------------
    // Output pipeline register
    // -----------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            mult_valid_q    <= '0;
            trans_id_q      <= '0;
            operator_q      <=  MUL;
            mult_result_q   <= '0;
         end else begin
            // Input silencing
            trans_id_q   <= trans_id_i;
            // Output Register
            mult_valid_q    <= mult_valid;
            operator_q      <= operator_d;
            mult_result_q   <= mult_result_d;
         end
    end
endmodule
