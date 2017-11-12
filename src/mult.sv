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

module mult (
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


    // mul (
    //     .*
    // );
    // enum logic { IDLE, DIV } state_d, state_q;

    // // ----------------
    // // Mock Multiplier
    // // ----------------
    // assign mult_trans_id_o = trans_id_i;
    // assign mult_ready_o    = 1'b1;

    // // sign extend operand a and b
    // logic sign_a, sign_b;

    // logic [1:0]   opcode_div;


    // always_comb begin : mul_div

    //     // perform multiplication

    //     result_o = '0;
    //     sign_a   = 1'b0;
    //     sign_b   = 1'b0;
    //     state_d  = state_q;

    //     case (state_q)
    //         // Unit is idle
    //         IDLE: begin
    //             // Operand select
    //             case (operator_i)
    //                 // MUL performs an XLEN-bit×XLEN-bit multiplication and places the lower XLEN bits in the destination register
    //                 MUL:
    //                     result_o = mult_result[63:0];

    //                 MULH: begin
    //                     sign_a   = 1'b1;
    //                     sign_b   = 1'b1;
    //                     result_o = mult_result[127:64];
    //                 end

    //                 MULHU:
    //                     result_o = mult_result[127:64];

    //                 MULHSU: begin
    //                     sign_a   = 1'b1;
    //                     result_o = mult_result[127:64];
    //                 end

    //                 MULW:
    //                     result_o = sign_extend(mult_result[31:0]);

    //                 // Divisions
    //                 DIV: begin
    //                     result_o = $signed(operand_a_i) / $signed(operand_b_i);
    //                     // division by zero
    //                     // set all bits
    //                     if (operand_b_i == '0)
    //                         result_o = -1;
    //                 end

    //                 DIVU: begin
    //                     result_o = operand_a_i / operand_b_i;
    //                     // division by zero
    //                     // set all bits
    //                     if (operand_b_i == '0)
    //                         result_o = -1;
    //                 end

    //                 DIVW: begin
    //                     result_o = sign_extend($signed(operand_a_i[31:0]) / $signed(operand_b_i[31:0]));
    //                     // division by zero
    //                     // set all bits
    //                     if (operand_b_i == '0)
    //                         result_o = -1;
    //                 end

    //                 DIVUW: begin
    //                     result_o = sign_extend(operand_a_i[31:0] / operand_b_i[31:0]);
    //                     // division by zero
    //                     // set all bits
    //                     if (operand_b_i == '0)
    //                         result_o = -1;
    //                 end

    //                 REM: begin
    //                     result_o = $signed(operand_a_i) % $signed(operand_b_i);
    //                     // division by zero
    //                     if (operand_b_i == '0)
    //                         result_o = operand_a_i;
    //                 end

    //                 REMU: begin
    //                     result_o = operand_a_i % operand_b_i;
    //                     // division by zero
    //                     if (operand_b_i == '0)
    //                         result_o = operand_a_i;
    //                 end

    //                 REMW: begin
    //                     result_o = sign_extend($signed(operand_a_i[31:0]) % $signed(operand_b_i[31:0]));
    //                     // division by zero
    //                     if (operand_b_i == '0)
    //                         result_o = operand_a_i;
    //                 end

    //                 REMUW: begin
    //                     result_o = sign_extend(operand_a_i[31:0] % operand_b_i[31:0]);
    //                     // division by zero
    //                     if (operand_b_i == '0)
    //                         result_o = operand_a_i;
    //                 end
    //             endcase
    //         end
    //         // unit is dividing
    //         DIV: begin


    //         end
    //     endcase
    // end

//divu
    serial_divider #(
        .C_WIDTH      ( 64                   ),
        .C_LOG_WIDTH  ( $clog2(64) + 1       )
    ) i_div (
        .Clk_CI       ( clk_i                ),
        .Rst_RBI      ( rst_ni               ),
        .TransId_DI   ( trans_id_i           ),
        .OpA_DI       ( operand_a_i          ),
        .OpB_DI       ( operand_b_i          ),
        .OpBShift_DI  ( 7'd64                ),
        .OpBIsZero_SI ( (operand_b_i == '0)  ),
        .OpBSign_SI   ( '0                   ), // gate this to 0 in case of unsigned ops
        .OpCode_SI    ( '0                   ), // 0: udiv, 2: urem, 1: div, 3: rem
        .InVld_SI     ( mult_valid_i         ),
        .OutRdy_SI    ( 1'b1                 ),
        .OutVld_SO    ( mult_valid_o         ),
        .TransId_DO   ( mult_trans_id_o      ),
        .Res_DO       ( result_o             )
    );

    // // Registers
    // always_ff @(posedge clk_i or negedge rst_ni) begin
    //     if (~rst_ni) begin
    //         state_q <= IDLE;
    //     end else begin
    //         state_q <= state_d;
    //     end
    // end
endmodule

///////////////////////////////////////////////////////////////////////////////
// File       : Simple Serial Divider
// Ver        : 1.0
// Date       : 15.03.2016
///////////////////////////////////////////////////////////////////////////////
//
// Description: this is a simple serial divider for signed integers.
//
///////////////////////////////////////////////////////////////////////////////
//
// Authors    : Michael Schaffner (schaffner@iis.ee.ethz.ch)
//              Andreas Traber    (atraber@iis.ee.ethz.ch)
//
///////////////////////////////////////////////////////////////////////////////
module serial_divider #(
    parameter int unsigned C_WIDTH     = 32,
    parameter int unsigned C_LOG_WIDTH = 6
) (
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
    // output IF
    input  logic                      OutRdy_SI,
    output logic                      OutVld_SO,
    output logic [TRANS_ID_BITS-1:0]  TransId_DO,
    output logic [C_WIDTH-1:0]        Res_DO
);

    ///////////////////////////////////////////////////////////////////////////////
    // signal declarations
    ///////////////////////////////////////////////////////////////////////////////
    logic [C_WIDTH-1:0]       ResReg_DP, ResReg_DN;
    logic [C_WIDTH-1:0]       ResReg_DP_rev;
    logic [C_WIDTH-1:0]       AReg_DP, AReg_DN;
    logic [C_WIDTH-1:0]       BReg_DP, BReg_DN;
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


    ///////////////////////////////////////////////////////////////////////////////
    // datapath
    ///////////////////////////////////////////////////////////////////////////////

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
    assign ABComp_S = ((AReg_DP == BReg_DP) | ((AReg_DP > BReg_DP) ^ CompInv_SP)) & ((|AReg_DP) | OpBIsZero_SI);

    // main adder
    assign AddTmp_D = (LoadEn_S) ? 0 : AReg_DP;
    assign AddOut_D = (PmSel_S)  ? AddTmp_D + AddMux_D : AddTmp_D - $signed(AddMux_D);

    ///////////////////////////////////////////////////////////////////////////////
    // counter
    ///////////////////////////////////////////////////////////////////////////////

    assign Cnt_DN = (LoadEn_S)   ? OpBShift_DI :
        (~CntZero_S) ? Cnt_DP - 1  : Cnt_DP;

    assign CntZero_S = ~(|Cnt_DP);

    ///////////////////////////////////////////////////////////////////////////////
    // FSM
    ///////////////////////////////////////////////////////////////////////////////

    always_comb
        begin : p_fsm
            // default
            State_SN       = State_SP;

            OutVld_SO      = 1'b0;

            LoadEn_S       = 1'b0;

            ARegEn_S       = 1'b0;
            BRegEn_S       = 1'b0;
            ResRegEn_S     = 1'b0;

            case (State_SP)
                /////////////////////////////////
                IDLE: begin
                    OutVld_SO    = 1'b1;

                    if(InVld_SI) begin
                        OutVld_SO  = 1'b0;
                        ARegEn_S   = 1'b1;
                        BRegEn_S   = 1'b1;
                        LoadEn_S   = 1'b1;
                        State_SN   = DIVIDE;
                    end
                end
                /////////////////////////////////
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
                /////////////////////////////////
                FINISH: begin
                    OutVld_SO = 1'b1;

                    if(OutRdy_SI) begin
                        State_SN  = IDLE;
                    end
                end
                /////////////////////////////////
                default : /* default */ ;
                /////////////////////////////////
            endcase
        end


    ///////////////////////////////////////////////////////////////////////////////
    // regs
    ///////////////////////////////////////////////////////////////////////////////

    // get flags
    assign RemSel_SN  = (LoadEn_S) ? OpCode_SI[1] : RemSel_SP;
    assign CompInv_SN = (LoadEn_S) ? OpBSign_SI   : CompInv_SP;
    assign ResInv_SN  = (LoadEn_S) ? (~OpBIsZero_SI | OpCode_SI[1]) & OpCode_SI[0] & (OpA_DI[$high(OpA_DI)] ^ OpBSign_SI) : ResInv_SP;

    // transaction id
    assign TransId_DN = (LoadEn_S) ? TransId_DI : TransId_DP;
    assign TransId_DO = TransId_DP;

    assign AReg_DN   = (ARegEn_S)   ? AddOut_D : AReg_DP;
    assign BReg_DN   = (BRegEn_S)   ? BMux_D   : BReg_DP;
    assign ResReg_DN = (LoadEn_S)   ? '0       :
        (ResRegEn_S) ? {ABComp_S, ResReg_DP[$high(ResReg_DP):1]} : ResReg_DP;

    always_ff @(posedge Clk_CI or negedge Rst_RBI) begin : p_regs
        if (~Rst_RBI) begin
            State_SP   <= IDLE;
            AReg_DP    <= '0;
            BReg_DP    <= '0;
            ResReg_DP  <= '0;
            Cnt_DP     <= '0;
            TransId_DP <= '0;
            RemSel_SP  <= 1'b0;
            CompInv_SP <= 1'b0;
            ResInv_SP  <= 1'b0;
        end else begin
            State_SP   <= State_SN;
            AReg_DP    <= AReg_DN;
            BReg_DP    <= BReg_DN;
            ResReg_DP  <= ResReg_DN;
            Cnt_DP     <= Cnt_DN;
            TransId_DP <= TransId_DN;
            RemSel_SP  <= RemSel_SN;
            CompInv_SP <= CompInv_SN;
            ResInv_SP  <= ResInv_SN;
        end
    end

    ///////////////////////////////////////////////////////////////////////////////
    // assertions
    ///////////////////////////////////////////////////////////////////////////////

    `ifndef SYNTHESIS
        initial begin : p_assertions
            assert (C_LOG_WIDTH == $clog2(C_WIDTH+1)) else $error("C_LOG_WIDTH must be $clog2(C_WIDTH+1)");
        end
    `endif

endmodule // serDiv

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
    logic [63:0]                operand_a_q;
    logic [63:0]                operand_b_q;
    fu_op                       operator_q;
    logic                       sign_a_q, sign_b_q;

    // control signals
    assign mult_valid_o    = mult_valid_q;
    assign mult_trans_id_o = trans_id_q;
    assign mult_ready_o    = 1'b1;
    // datapath
    logic [127:0] mult_result;
    assign mult_result   = $signed({operand_a_q[63] & sign_a_q, operand_a_q}) * $signed({operand_b_q[63] & sign_b_q, operand_b_q});

    // Output MUX
    always_comb begin
        case (operator_q)
            // MUL performs an XLEN-bit×XLEN-bit multiplication and places the lower XLEN bits in the destination register
            MUL:    result_o = mult_result[63:0];
            MULH:   result_o = mult_result[127:64];
            MULHU:  result_o = mult_result[127:64];
            MULHSU: result_o = mult_result[127:64];
            MULW:   result_o = sign_extend(mult_result[31:0]);
        endcase
    end
    // -----------------------
    // Input pipeline register
    // -----------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            mult_valid_q <= '0;
            trans_id_q   <= '0;
            operand_a_q  <= '0;
            operand_b_q  <= '0;
            operator_q   <= ADD;
            sign_a_q     <= '0;
            sign_b_q     <= '0;
        end else begin
            mult_valid_q <= mult_valid_i;
            // Input silencing
            if (mult_valid_i) begin
                trans_id_q   <= trans_id_i;
                operand_a_q  <= operand_a_i;
                operand_b_q  <= operand_b_i;
                operator_q   <= operator_i;
                // signed multiplication
                if (operator_i == MULH) begin
                    sign_a_q   <= 1'b1;
                    sign_b_q   <= 1'b1;
                // signed - unsigned multiplication
                end else if (operator_i == MULHSU) begin
                    sign_a_q   <= 1'b1;
                // unsigned multiplication
                end else begin
                    sign_a_q   <= 1'b0;
                    sign_b_q   <= 1'b0;
                end
            end
        end
    end
endmodule
