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
// Description: Ariane Multiplier

import ariane_pkg::*;

module mult (
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     flush_i,
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
    assign mul_valid_op = ~flush_i && mult_valid_i && (operator_i inside { MUL, MULH, MULHU, MULHSU, MULW });
    assign div_valid_op = ~flush_i && mult_valid_i && (operator_i inside { DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW });

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
        .result_o          ( mul_result   ),
        .mult_valid_i      ( mul_valid_op ),
        .mult_valid_o      ( mul_valid    ),
        .mult_trans_id_o   ( mul_trans_id ),
        .mult_ready_o      (              ), // this unit is unconditionally ready
        .*
    );

    // ---------------------
    // Division
    // ---------------------
    logic [5:0]  ff1_result; // holds the index of the last '1' (as the input operand is reversed)
    logic        ff1_no_one; // no one was found by find first one
    logic [63:0] ff1_input;  // input to find first one
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
    assign div_signed = (operator_i inside {DIV, DIVW, REM, REMW}) ? 1'b1 : 1'b0;
    // if this operation is signed look at the actual sign bit to determine whether we should perform signed or unsigned division
    assign div_op_signed = div_signed & operand_b[63];

    // reverse input operands
    generate
        for (genvar k = 0; k < 64; k++)
            assign operand_b_rev[k] = operand_b[63-k];
    endgenerate
    // negated reverse input operand, used for signed divisions
    assign operand_b_rev_neg = ~operand_b_rev;
    assign ff1_input = (div_op_signed) ? operand_b_rev_neg : operand_b_rev;

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
        if (mult_valid_i && operator_i inside {DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW}) begin
            // is this a word operation?
            if (operator_i inside {DIVW, DIVUW, REMW, REMUW}) begin
                word_op = 1'b1;
                // yes so check if we should sign extend this is only done for a signed operation
                if (div_signed) begin
                    operand_a = sext32(operand_a_i[31:0]);
                    operand_b = sext32(operand_b_i[31:0]);
                end else begin
                    operand_a = {32'b0, operand_a_i[31:0]};
                    operand_b = {32'b0, operand_b_i[31:0]};
                end

                // save whether we want sign extend the result or not, this is done for all word operations
                word_op_d = 1'b1;
            // regular operation
            end else begin
                word_op_d = 1'b0;
                // no sign extending is necessary as we are already using the full 64 bit
                operand_a = operand_a_i;
                operand_b = operand_b_i;
            end

            // is this a modulo?
            if (operator_i inside {REM, REMU, REMW, REMUW}) begin
                rem = 1'b1;
            end
        end
    end

    // ---------------------
    // Find First one
    // ---------------------
    // this unit is used to speed up the sequential division by shifting the dividend first
    alu_ff #(
        .LEN         ( 64         )
    ) i_ff1 (
        .in_i        ( ff1_input  ), // signed = operand_b_rev_neg, unsigned operand_b_rev
        .first_one_o ( ff1_result ),
        .no_ones_o   ( ff1_no_one )
    );

    // if the dividend is all zero go for the full length
    assign div_shift = ff1_no_one ? 7'd64 : ff1_result;
    // prepare dividend by shifting
    assign operand_b_shift = operand_b <<< div_shift;

    // ---------------------
    // Serial Divider
    // ---------------------
    serial_divider #(
        .C_WIDTH      ( 64                ),
        .C_LOG_WIDTH  ( $clog2(64) + 1    )
    ) i_div (
        .Clk_CI       ( clk_i             ),
        .Rst_RBI      ( rst_ni            ),
        .TransId_DI   ( trans_id_i        ),
        .OpA_DI       ( operand_a         ),
        .OpB_DI       ( operand_b_shift   ),
        .OpBShift_DI  ( div_shift         ),
        .OpBIsZero_SI ( ~(|operand_b)     ),
        .OpBSign_SI   ( div_op_signed     ), // gate this to 0 in case of unsigned ops
        .OpCode_SI    ( {rem, div_signed} ), // 00: udiv, 10: urem, 01: div, 11: rem
        .InVld_SI     ( div_valid_op      ),
        .Flush_SI     ( flush_i           ),
        .OutRdy_SO    ( mult_ready_o      ),
        .OutRdy_SI    ( div_ready_i       ),
        .OutVld_SO    ( div_valid         ),
        .TransId_DO   ( div_trans_id      ),
        .Res_DO       ( result            )
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

/* File       : mult.sv
 * Ver        : 1.0
 * Date       : 15.03.2016
 *
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 *
 * Description: this is a simple serial divider for signed integers.
 *
 *
 * Authors    : Michael Schaffner (schaffner@iis.ee.ethz.ch)
 *              Andreas Traber    (atraber@iis.ee.ethz.ch)
 *
 */
module serial_divider #(
    parameter int unsigned C_WIDTH     = 32,
    parameter int unsigned C_LOG_WIDTH = 6
)(
    input  logic                      Clk_CI,
    input  logic                      Rst_RBI,
    // input IF
    input  logic [TRANS_ID_BITS-1:0]  TransId_DI,
    input  logic [C_WIDTH-1:0]        OpA_DI,
    input  logic [C_WIDTH-1:0]        OpB_DI,
    input  logic [C_LOG_WIDTH-1:0]    OpBShift_DI,
    input  logic                      OpBIsZero_SI,
    //
    input  logic                      OpBSign_SI, // gate this to 0 in case of unsigned ops
    input  logic [1:0]                OpCode_SI,  // 0: udiv, 2: urem, 1: div, 3: rem
    // handshake
    input  logic                      InVld_SI,
    input  logic                      Flush_SI,
    // output IF
    output logic                      OutRdy_SO,
    input  logic                      OutRdy_SI,
    output logic                      OutVld_SO,
    output logic [TRANS_ID_BITS-1:0]  TransId_DO,
    output logic [C_WIDTH-1:0]        Res_DO
);

    // ----------------------------------
    // Signal Declarations
    // ----------------------------------
    logic [C_WIDTH-1:0]       ResReg_DP, ResReg_DN;
    logic [C_WIDTH-1:0]       ResReg_DP_rev;
    logic [C_WIDTH-1:0]       AReg_DP, AReg_DN;
    logic [C_WIDTH-1:0]       BReg_DP, BReg_DN;
    logic                     OpBIsZero_SP, OpBIsZero_SN;

    logic [TRANS_ID_BITS-1:0] TransId_DP, TransId_DN;

    logic RemSel_SN, RemSel_SP;
    logic CompInv_SN, CompInv_SP;
    logic ResInv_SN, ResInv_SP;

    logic [C_WIDTH-1:0] AddMux_D;
    logic [C_WIDTH-1:0] AddOut_D;
    logic [C_WIDTH-1:0] AddTmp_D;
    logic [C_WIDTH-1:0] BMux_D;
    logic [C_WIDTH-1:0] OutMux_D;

    logic [C_LOG_WIDTH-1:0] Cnt_DP, Cnt_DN;
    logic CntZero_S;

    logic ARegEn_S, BRegEn_S, ResRegEn_S, ABComp_S, PmSel_S, LoadEn_S;

    enum logic [1:0] {IDLE, DIVIDE, FINISH} State_SN, State_SP;


    // -----------------
    // Datapath
    // -----------------
    assign PmSel_S = LoadEn_S & ~(OpCode_SI[0] & (OpA_DI[$high(OpA_DI)] ^ OpBSign_SI));

    // muxes
    assign AddMux_D = (LoadEn_S) ? OpA_DI  : BReg_DP;

    // attention: logical shift in case of negative operand B!
    assign BMux_D = (LoadEn_S) ? OpB_DI : {CompInv_SP, (BReg_DP[$high(BReg_DP):1])};

    assign ResReg_DP_rev = {<<{ResReg_DP}};
    assign OutMux_D      = (RemSel_SP) ? AReg_DP : ResReg_DP_rev;

    // invert if necessary
    assign Res_DO = (ResInv_SP) ? -$signed(OutMux_D) : OutMux_D;

    // main comparator
    assign ABComp_S = ((AReg_DP == BReg_DP) | ((AReg_DP > BReg_DP) ^ CompInv_SP)) & ((|AReg_DP) | OpBIsZero_SP);

    // main adder
    assign AddTmp_D = (LoadEn_S) ? 0 : AReg_DP;
    assign AddOut_D = (PmSel_S)  ? AddTmp_D + AddMux_D : AddTmp_D - $signed(AddMux_D);

    // -----------------
    // Counter
    // -----------------
    assign Cnt_DN = (LoadEn_S)   ? OpBShift_DI :
        (~CntZero_S) ? Cnt_DP - 1  : Cnt_DP;

    assign CntZero_S = ~(|Cnt_DP);

    // -----------------
    // FSM
    // -----------------
    always_comb begin : p_fsm
            // default
            State_SN       = State_SP;

            OutVld_SO      = 1'b0;
            OutRdy_SO      = 1'b0;

            LoadEn_S       = 1'b0;

            ARegEn_S       = 1'b0;
            BRegEn_S       = 1'b0;
            ResRegEn_S     = 1'b0;

            case (State_SP)

                IDLE: begin
                    OutRdy_SO    = 1'b1;

                    if (InVld_SI) begin
                        OutRdy_SO  = 1'b0;
                        OutVld_SO  = 1'b0;
                        ARegEn_S   = 1'b1;
                        BRegEn_S   = 1'b1;
                        LoadEn_S   = 1'b1;
                        State_SN   = DIVIDE;
                    end
                end

                DIVIDE: begin

                    ARegEn_S     = ABComp_S;
                    BRegEn_S     = 1'b1;
                    ResRegEn_S   = 1'b1;

                    // calculation finished
                    // one more divide cycle (C_WIDTH th divide cycle)
                    if (CntZero_S) begin
                        State_SN   = FINISH;
                    end
                end

                FINISH: begin
                    OutVld_SO = 1'b1;

                    if (OutRdy_SI) begin
                        State_SN  = IDLE;
                    end
                end

                default : /* default */ ;

            endcase

            if (Flush_SI) begin
                OutRdy_SO  = 1'b0;
                OutVld_SO  = 1'b0;
                ARegEn_S   = 1'b0;
                BRegEn_S   = 1'b0;
                LoadEn_S   = 1'b0;
                State_SN   = IDLE;
            end
        end

    // -----------------
    //  Registers
    // -----------------
    // get flags
    assign RemSel_SN    = (LoadEn_S) ? OpCode_SI[1] : RemSel_SP;
    assign CompInv_SN   = (LoadEn_S) ? OpBSign_SI   : CompInv_SP;
    assign OpBIsZero_SN = (LoadEn_S) ? OpBIsZero_SI : OpBIsZero_SP;
    assign ResInv_SN    = (LoadEn_S) ? (~OpBIsZero_SI | OpCode_SI[1]) & OpCode_SI[0] & (OpA_DI[$high(OpA_DI)] ^ OpBSign_SI) : ResInv_SP;

    // transaction id
    assign TransId_DN = (LoadEn_S) ? TransId_DI : TransId_DP;
    assign TransId_DO = TransId_DP;

    assign AReg_DN   = (ARegEn_S)   ? AddOut_D : AReg_DP;
    assign BReg_DN   = (BRegEn_S)   ? BMux_D   : BReg_DP;
    assign ResReg_DN = (LoadEn_S)   ? '0       :
        (ResRegEn_S) ? {ABComp_S, ResReg_DP[$high(ResReg_DP):1]} : ResReg_DP;

    always_ff @(posedge Clk_CI or negedge Rst_RBI) begin : p_regs
        if (~Rst_RBI) begin
            State_SP     <= IDLE;
            AReg_DP      <= '0;
            BReg_DP      <= '0;
            ResReg_DP    <= '0;
            Cnt_DP       <= '0;
            TransId_DP   <= '0;
            RemSel_SP    <= 1'b0;
            CompInv_SP   <= 1'b0;
            ResInv_SP    <= 1'b0;
            OpBIsZero_SP <= 1'b0;
        end else begin
            State_SP     <= State_SN;
            AReg_DP      <= AReg_DN;
            BReg_DP      <= BReg_DN;
            ResReg_DP    <= ResReg_DN;
            Cnt_DP       <= Cnt_DN;
            TransId_DP   <= TransId_DN;
            RemSel_SP    <= RemSel_SN;
            CompInv_SP   <= CompInv_SN;
            ResInv_SP    <= ResInv_SN;
            OpBIsZero_SP <= OpBIsZero_SN;
        end
    end

    // ------------
    // Assertions
    // ------------
    `ifndef SYNTHESIS
        initial begin : p_assertions
            assert (C_LOG_WIDTH == $clog2(C_WIDTH+1)) else $error("C_LOG_WIDTH must be $clog2(C_WIDTH+1)");
        end
    `endif

endmodule

// --------------------------------------------------
// Multiplication Unit with one pipeline register
// --------------------------------------------------
module mul (
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
    // Pipeline register
    logic [TRANS_ID_BITS-1:0]   trans_id_q;
    logic                       mult_valid_q;
    logic [63:0]                result_q;
    // control registers
    logic                       sign_a, sign_b;
    logic                       mult_valid;

    // control signals
    assign mult_valid_o    = mult_valid_q;
    assign result_o        = result_q;
    assign mult_trans_id_o = trans_id_q;
    assign mult_ready_o    = 1'b1;

    assign mult_valid      = mult_valid_i && (operator_i inside {MUL, MULH, MULHU, MULHSU, MULW});
    // datapath
    logic [127:0] mult_result;
    assign mult_result   = $signed({operand_a_i[63] & sign_a, operand_a_i}) * $signed({operand_b_i[63] & sign_b, operand_b_i});

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

    // -----------------------
    // Output pipeline register
    // -----------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            mult_valid_q <= '0;
            trans_id_q   <= '0;
            result_q     <= '0;
        end else begin
            // Input silencing
            trans_id_q   <= trans_id_i;
            // Output Register
            mult_valid_q <= mult_valid;

            case (operator_i)
                // MUL performs an XLEN-bit×XLEN-bit multiplication and places the lower XLEN bits in the destination register
                MUL:    result_q <= mult_result[63:0];
                MULH:   result_q <= mult_result[127:64];
                MULHU:  result_q <= mult_result[127:64];
                MULHSU: result_q <= mult_result[127:64];
                MULW:   result_q <= sext32(mult_result[31:0]);
            endcase
        end
    end
endmodule

// -----------------
// Find First One
// -----------------
module alu_ff #(
    parameter int unsigned LEN = 32
)(
    input  logic [LEN-1:0]         in_i,
    output logic [$clog2(LEN)-1:0] first_one_o,
    output logic                   no_ones_o
);

    localparam int unsigned NUM_LEVELS = $clog2(LEN);

    logic [LEN-1:0] [NUM_LEVELS-1:0]           index_lut;
    logic [2**NUM_LEVELS-1:0]                  sel_nodes;
    logic [2**NUM_LEVELS-1:0] [NUM_LEVELS-1:0] index_nodes;

    // ----------------------------
    // Generate Tree Structure
    // ----------------------------
    generate
        for (genvar j = 0; j < LEN; j++) begin
            assign index_lut[j] = $unsigned(j);
        end
    endgenerate

    generate
        for (genvar level = 0; level < NUM_LEVELS; level++) begin

            if (level < NUM_LEVELS-1) begin
                for (genvar l = 0; l < 2**level; l++) begin
                    assign sel_nodes[2**level-1+l]   = sel_nodes[2**(level+1)-1+l*2] | sel_nodes[2**(level+1)-1+l*2+1];
                    assign index_nodes[2**level-1+l] = (sel_nodes[2**(level+1)-1+l*2] == 1'b1) ?
                        index_nodes[2**(level+1)-1+l*2] : index_nodes[2**(level+1)-1+l*2+1];
                end
            end

            if (level == NUM_LEVELS-1) begin
                for (genvar k = 0; k < 2**level; k++) begin
                    // if two successive indices are still in the vector...
                    if (k * 2 < LEN) begin
                        assign sel_nodes[2**level-1+k]   = in_i[k*2] | in_i[k*2+1];
                        assign index_nodes[2**level-1+k] = (in_i[k*2] == 1'b1) ? index_lut[k*2] : index_lut[k*2+1];
                    end
                    // if only the first index is still in the vector...
                    if (k * 2 == LEN) begin
                        assign sel_nodes[2**level-1+k]   = in_i[k*2];
                        assign index_nodes[2**level-1+k] = index_lut[k*2];
                    end
                    // if index is out of range
                    if (k * 2 > LEN) begin
                        assign sel_nodes[2**level-1+k]   = 1'b0;
                        assign index_nodes[2**level-1+k] = '0;
                    end
                end
            end
        end
    endgenerate

    // --------------------
    // Connect Output
    // --------------------
    assign first_one_o = index_nodes[0];
    assign no_ones_o   = ~sel_nodes[0];

endmodule
