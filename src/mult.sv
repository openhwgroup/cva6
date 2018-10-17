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
// Date: 05.06.2017
// Description: Ariane Multiplier and Divider (as defined in the M-extension)

import ariane_pkg::*;

module mult (
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     flush_i,
    input  fu_data_t                 fu_data_i,
    input  logic                     mult_valid_i,
    output logic [63:0]              result_o,
    output logic                     mult_valid_o,
    output logic                     mult_ready_o,
    output logic [TRANS_ID_BITS-1:0] mult_trans_id_o
);
    logic                     mul_valid;
    logic                     div_valid;
    logic                     div_ready_i; // receiver of division result is able to accept the result
    logic [TRANS_ID_BITS-1:0] mul_trans_id;
    logic [TRANS_ID_BITS-1:0] div_trans_id;
    logic [63:0]              mul_result;
    logic [63:0]              div_result;

    logic                     div_valid_op;
    logic                     mul_valid_op;
    // Input Arbitration
    assign mul_valid_op = ~flush_i && mult_valid_i && (fu_data_i.operator inside { MUL, MULH, MULHU, MULHSU, MULW });
    assign div_valid_op = ~flush_i && mult_valid_i && (fu_data_i.operator inside { DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW });

    // ---------------------
    // Output Arbitration
    // ---------------------
    // we give precedence to multiplication as the divider supports stalling and the multiplier is
    // just a dumb pipelined multiplier
    assign div_ready_i      = (mul_valid) ? 1'b0         : 1'b1;
    assign mult_trans_id_o  = (mul_valid) ? mul_trans_id : div_trans_id;
    assign result_o         = (mul_valid) ? mul_result   : div_result;
    assign mult_valid_o     = div_valid | mul_valid;
    // mult_ready_o = division as the multiplication will unconditionally be ready to accept new requests

    // ---------------------
    // Multiplication
    // ---------------------
    mul i_mul (
        .clk_i,
        .rst_ni,
        .trans_id_i        ( fu_data_i.trans_id  ),
        .operator_i        ( fu_data_i.operator  ),
        .operand_a_i       ( fu_data_i.operand_a ),
        .operand_b_i       ( fu_data_i.operand_b ),
        .result_o          ( mul_result   ),
        .mult_valid_i      ( mul_valid_op ),
        .mult_valid_o      ( mul_valid    ),
        .mult_trans_id_o   ( mul_trans_id ),
        .mult_ready_o      (              ) // this unit is unconditionally ready
    );

    // ---------------------
    // Division
    // ---------------------
    logic [5:0]  lzc_result; // holds the index of the last '1' (as the input operand is reversed)
    logic        lzc_no_one; // no one was found by find first one
    logic [63:0] lzc_input;  // input to find first one
    logic [63:0] operand_b_rev, operand_b_rev_neg, operand_b_shift; // couple of different representations for the dividend
    logic [6:0]  div_shift;             // amount of which to shift to left
    logic        div_signed;            // should this operation be performed as a signed or unsigned division
    logic        div_op_signed;         // actual sign signal depends on div_signed and the MSB of the word
    logic [63:0] operand_b, operand_a;  // input operands after input MUX (input silencing, word operations or full inputs)
    logic [63:0] result;                // result before result mux

    logic        word_op;               // is it a word operation
    logic        rem;                   // is it a reminder (or not a reminder e.g.: a division)
    logic        word_op_d, word_op_q;  // save whether the operation was signed or not

    // is this a signed operation?
    assign div_signed = (fu_data_i.operator inside {DIV, DIVW, REM, REMW}) ? 1'b1 : 1'b0;
    // if this operation is signed look at the actual sign bit to determine whether we should perform signed or unsigned division
    assign div_op_signed = div_signed & operand_b[63];

    // reverse input operands
    generate
        for (genvar k = 0; k < 64; k++)
            assign operand_b_rev[k] = operand_b[63-k];
    endgenerate
    // negated reverse input operand, used for signed divisions
    assign operand_b_rev_neg = ~operand_b_rev;
    assign lzc_input = (div_op_signed) ? operand_b_rev_neg : operand_b_rev;

    // prepare the input operands and control divider
    always_comb begin
        // silence the inputs
        operand_a   = '0;
        operand_b   = '0;
        // control signals
        word_op_d = word_op_q;
        word_op     = 1'b0;
        rem         = 1'b0;

        // we've go a new division operation
        if (mult_valid_i && fu_data_i.operator inside {DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW}) begin
            // is this a word operation?
            if (fu_data_i.operator inside {DIVW, DIVUW, REMW, REMUW}) begin
                word_op = 1'b1;
                // yes so check if we should sign extend this is only done for a signed operation
                if (div_signed) begin
                    operand_a = sext32(fu_data_i.operand_a[31:0]);
                    operand_b = sext32(fu_data_i.operand_b[31:0]);
                end else begin
                    operand_a = {32'b0, fu_data_i.operand_a[31:0]};
                    operand_b = {32'b0, fu_data_i.operand_b[31:0]};
                end

                // save whether we want sign extend the result or not, this is done for all word operations
                word_op_d = 1'b1;
            // regular operation
            end else begin
                word_op_d = 1'b0;
                // no sign extending is necessary as we are already using the full 64 bit
                operand_a = fu_data_i.operand_a;
                operand_b = fu_data_i.operand_b;
            end

            // is this a modulo?
            if (fu_data_i.operator inside {REM, REMU, REMW, REMUW}) begin
                rem = 1'b1;
            end
        end
    end

    // ---------------------
    // Leading Zero Counter
    // ---------------------
    // this unit is used to speed up the sequential division by shifting the dividend first
    lzc #(
        .WIDTH   ( 64         )
    ) i_lzc (
        .in_i    ( lzc_input  ), // signed = operand_b_rev_neg, unsigned operand_b_rev
        .cnt_o   ( lzc_result ),
        .empty_o ( lzc_no_one )
    );

    // if the dividend is all zero go for the full length
    assign div_shift = lzc_no_one ? 7'd64 : lzc_result;
    // prepare dividend by shifting
    assign operand_b_shift = operand_b <<< div_shift;

    // ---------------------
    // Serial Divider
    // ---------------------
    serial_divider #(
        .C_WIDTH      ( 64                ),
        .C_LOG_WIDTH  ( $clog2(64) + 1    )
    ) i_div (
        .Clk_CI       ( clk_i              ),
        .Rst_RBI      ( rst_ni             ),
        .TransId_DI   ( fu_data_i.trans_id ),
        .OpA_DI       ( operand_a          ),
        .OpB_DI       ( operand_b_shift    ),
        .OpBShift_DI  ( div_shift          ),
        .OpBIsZero_SI ( ~(|operand_b)      ),
        .OpBSign_SI   ( div_op_signed      ), // gate this to 0 in case of unsigned ops
        .OpCode_SI    ( {rem, div_signed}  ), // 00: udiv, 10: urem, 01: div, 11: rem
        .InVld_SI     ( div_valid_op       ),
        .Flush_SI     ( flush_i            ),
        .OutRdy_SO    ( mult_ready_o       ),
        .OutRdy_SI    ( div_ready_i        ),
        .OutVld_SO    ( div_valid          ),
        .TransId_DO   ( div_trans_id       ),
        .Res_DO       ( result             )
    );
    // Result multiplexer
    // if it was a signed word operation the bit will be set and the result will be sign extended accordingly
    assign div_result = (word_op_q) ? sext32(result) : result;

    // ---------------------
    // Registers
    // ---------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            word_op_q <= ADD;
        end else begin
            word_op_q <= word_op_d;
        end
    end
endmodule
