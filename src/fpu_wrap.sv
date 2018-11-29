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
// Author: Stefan Mach, ETH Zurich
// Date: 12.04.2018
// Description: Wrapper for the floating-point unit

import ariane_pkg::*;

module fpu_wrap (
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     flush_i,
    input  logic                     fpu_valid_i,
    output logic                     fpu_ready_o,
    input  fu_data_t                 fu_data_i,

    input  logic [1:0]               fpu_fmt_i,
    input  logic [2:0]               fpu_rm_i,
    input  logic [2:0]               fpu_frm_i,
    input  logic [6:0]               fpu_prec_i,
    output logic [TRANS_ID_BITS-1:0] fpu_trans_id_o,
    output logic [FLEN-1:0]          result_o,
    output logic                     fpu_valid_o,
    output exception_t               fpu_exception_o
);

// this is a workaround
// otherwise compilation might issue an error if FLEN=0
generate
    if (FP_PRESENT) begin : fpu_gen

        logic [FLEN-1:0] operand_a_i;
        logic [FLEN-1:0] operand_b_i;
        logic [FLEN-1:0] operand_c_i;
        assign operand_a_i = fu_data_i.operand_a[FLEN-1:0];
        assign operand_b_i = fu_data_i.operand_b[FLEN-1:0];
        assign operand_c_i = fu_data_i.imm[FLEN-1:0];

        //-----------------------------------
        // FPnew encoding from FPnew package
        //-----------------------------------
        localparam OPBITS  =  4;
        localparam FMTBITS =  3;
        localparam IFMTBITS = 2;

        integer OP_NUMBITS, FMT_NUMBITS, IFMT_NUMBITS;

        logic [OPBITS-1:0] OP_FMADD;
        logic [OPBITS-1:0] OP_FNMSUB;
        logic [OPBITS-1:0] OP_ADD;
        logic [OPBITS-1:0] OP_MUL;
        logic [OPBITS-1:0] OP_DIV;
        logic [OPBITS-1:0] OP_SQRT;
        logic [OPBITS-1:0] OP_SGNJ;
        logic [OPBITS-1:0] OP_MINMAX;
        logic [OPBITS-1:0] OP_CMP;
        logic [OPBITS-1:0] OP_CLASS;
        logic [OPBITS-1:0] OP_F2I;
        logic [OPBITS-1:0] OP_I2F;
        logic [OPBITS-1:0] OP_F2F;
        logic [OPBITS-1:0] OP_CPKAB;
        logic [OPBITS-1:0] OP_CPKCD;

        logic [FMTBITS-1:0] FMT_FP32;
        logic [FMTBITS-1:0] FMT_FP64;
        logic [FMTBITS-1:0] FMT_FP16;
        logic [FMTBITS-1:0] FMT_FP8;
        logic [FMTBITS-1:0] FMT_FP16ALT;
        logic [FMTBITS-1:0] FMT_CUST1;
        logic [FMTBITS-1:0] FMT_CUST2;
        logic [FMTBITS-1:0] FMT_CUST3;

        logic [IFMTBITS-1:0] IFMT_INT8;
        logic [IFMTBITS-1:0] IFMT_INT16;
        logic [IFMTBITS-1:0] IFMT_INT32;
        logic [IFMTBITS-1:0] IFMT_INT64;

        // bind the constants from the fpnew entity
        fpnew_pkg_constants i_fpnew_constants (
            .OP_NUMBITS   ( OP_NUMBITS   ),
            .OP_FMADD     ( OP_FMADD     ),
            .OP_FNMSUB    ( OP_FNMSUB    ),
            .OP_ADD       ( OP_ADD       ),
            .OP_MUL       ( OP_MUL       ),
            .OP_DIV       ( OP_DIV       ),
            .OP_SQRT      ( OP_SQRT      ),
            .OP_SGNJ      ( OP_SGNJ      ),
            .OP_MINMAX    ( OP_MINMAX    ),
            .OP_CMP       ( OP_CMP       ),
            .OP_CLASS     ( OP_CLASS     ),
            .OP_F2I       ( OP_F2I       ),
            .OP_I2F       ( OP_I2F       ),
            .OP_F2F       ( OP_F2F       ),
            .OP_CPKAB     ( OP_CPKAB     ),
            .OP_CPKCD     ( OP_CPKCD     ),
            .FMT_NUMBITS  ( FMT_NUMBITS  ),
            .FMT_FP32     ( FMT_FP32     ),
            .FMT_FP64     ( FMT_FP64     ),
            .FMT_FP16     ( FMT_FP16     ),
            .FMT_FP8      ( FMT_FP8      ),
            .FMT_FP16ALT  ( FMT_FP16ALT  ),
            .FMT_CUST1    ( FMT_CUST1    ),
            .FMT_CUST2    ( FMT_CUST2    ),
            .FMT_CUST3    ( FMT_CUST3    ),
            .IFMT_NUMBITS ( IFMT_NUMBITS ),
            .IFMT_INT8    ( IFMT_INT8    ),
            .IFMT_INT16   ( IFMT_INT16   ),
            .IFMT_INT32   ( IFMT_INT32   ),
            .IFMT_INT64   ( IFMT_INT64   )
        );

        // always_comb begin
        //     assert (OPBITS >= OP_NUMBITS) else $error("OPBITS is smaller than %0d", OP_NUMBITS);
        //     assert (FMTBITS >= FMT_NUMBITS) else $error("FMTBITS is smaller than %0d", FMT_NUMBITS);
        //     assert (IFMTBITS >= IFMT_NUMBITS) else $error("IFMTBITS is smaller than %0d", IFMT_NUMBITS);
        // end

        //-------------------------------------------------
        // Inputs to the FPU and protocol inversion buffer
        //-------------------------------------------------
        logic [FLEN-1:0]     operand_a_d,  operand_a_q,  operand_a;
        logic [FLEN-1:0]     operand_b_d,  operand_b_q,  operand_b;
        logic [FLEN-1:0]     operand_c_d,  operand_c_q,  operand_c;
        logic [OPBITS-1:0]   fpu_op_d,     fpu_op_q,     fpu_op;
        logic                fpu_op_mod_d, fpu_op_mod_q, fpu_op_mod;
        logic [FMTBITS-1:0]  fpu_fmt_d,    fpu_fmt_q,    fpu_fmt;
        logic [FMTBITS-1:0]  fpu_fmt2_d,   fpu_fmt2_q,   fpu_fmt2;
        logic [IFMTBITS-1:0] fpu_ifmt_d,   fpu_ifmt_q,   fpu_ifmt;
        logic [2:0]          fpu_rm_d,     fpu_rm_q,     fpu_rm;
        logic                fpu_vec_op_d, fpu_vec_op_q, fpu_vec_op;

        logic [TRANS_ID_BITS-1:0] fpu_tag_d, fpu_tag_q, fpu_tag;

        logic fpu_in_ready, fpu_in_valid;
        logic fpu_out_ready, fpu_out_valid;

        logic [4:0] fpu_status;

        // FSM to handle protocol inversion
        enum logic {READY, STALL} state_q, state_d;
        logic hold_inputs;
        logic use_hold;

        //-----------------------------
        // Translate inputs
        //-----------------------------

        always_comb begin : input_translation

            automatic logic vec_replication; // control honoring of replication flag
            automatic logic replicate_c;     // replicate operand C instead of B (for ADD/SUB)
            automatic logic check_ah;        // Decide for AH from RM field encoding

            // Default Values
            operand_a_d         = operand_a_i;
            operand_b_d         = operand_b_i; // immediates come through this port unless used as operand
            operand_c_d         = operand_c_i; // immediates come through this port unless used as operand
            fpu_op_d            = OP_SGNJ; // sign injection by default
            fpu_op_mod_d        = 1'b0;
            fpu_fmt_d           = FMT_FP32;
            fpu_fmt2_d          = FMT_FP32;
            fpu_ifmt_d          = IFMT_INT32;
            fpu_rm_d            = fpu_rm_i;
            fpu_vec_op_d        = fu_data_i.fu == FPU_VEC;
            fpu_tag_d           = fu_data_i.trans_id;
            vec_replication     = fpu_rm_i[0]; // replication bit is sent via rm field
            replicate_c         = 1'b0;
            check_ah            = 1'b0; // whether set scalar AH encoding from MSB of rm_i

            // Scalar Rounding Modes - some ops encode inside RM but use smaller range
            if (!(fpu_rm_i inside {[3'b000:3'b100]}))
                fpu_rm_d = fpu_frm_i;

            // Vectorial ops always consult FRM
            if (fpu_vec_op_d)
                fpu_rm_d = fpu_frm_i;

            // Formats
            unique case (fpu_fmt_i)
                // FP32
                2'b00 : fpu_fmt_d = FMT_FP32;
                // FP64 or FP16ALT (vectorial)
                2'b01 : fpu_fmt_d = fpu_vec_op_d ? FMT_FP16ALT : FMT_FP64;
                // FP16 or FP16ALT (scalar)
                2'b10 : begin
                   if (!fpu_vec_op_d && fpu_rm_i==3'b101)
                       fpu_fmt_d = FMT_FP16ALT;
                   else
                       fpu_fmt_d = FMT_FP16;
                end
                // FP8
                default : fpu_fmt_d = FMT_FP8;
            endcase


            // Operations (this can modify the rounding mode field and format!)
            unique case (fu_data_i.operator)
                // Addition
                FADD      : begin
                    fpu_op_d    = OP_ADD;
                    replicate_c = 1'b1; // second operand is in C
                end
                // Subtraction is modified ADD
                FSUB      : begin
                    fpu_op_d     = OP_ADD;
                    fpu_op_mod_d = 1'b1;
                    replicate_c  = 1'b1; // second operand is in C
                end
                // Multiplication
                FMUL      : fpu_op_d = OP_MUL;
                // Division
                FDIV      : fpu_op_d = OP_DIV;
                // Min/Max - OP is encoded in rm (000-001)
                FMIN_MAX  : begin
                    fpu_op_d = OP_MINMAX;
                    fpu_rm_d = {1'b0, fpu_rm_i[1:0]}; // mask out AH encoding bit
                    check_ah = 1'b1; // AH has RM MSB encoding
                end
                // Square Root
                FSQRT     : fpu_op_d = OP_SQRT;
                // Fused Multiply Add
                FMADD     : fpu_op_d = OP_FMADD;
                // Fused Multiply Subtract is modified FMADD
                FMSUB     : begin
                    fpu_op_d     = OP_FMADD;
                    fpu_op_mod_d = 1'b1;
                end
                // Fused Negated Multiply Subtract
                FNMSUB    : fpu_op_d = OP_FNMSUB;
                // Fused Negated Multiply Add is modified FNMSUB
                FNMADD    : begin
                    fpu_op_d     = OP_FNMSUB;
                    fpu_op_mod_d = 1'b1;
                end
                // Float to Int Cast - Op encoded in lowest two imm bits or rm
                FCVT_F2I  : begin
                    fpu_op_d     = OP_F2I;
                    // Vectorial Ops encoded in R bit
                    if (fpu_vec_op_d) begin
                        fpu_op_mod_d      = fpu_rm_i[0];
                        vec_replication = 1'b0; // no replication, R bit used for op
                        unique case (fpu_fmt_i)
                            2'b00 : fpu_ifmt_d = IFMT_INT32;
                            2'b01,
                            2'b10 : fpu_ifmt_d = IFMT_INT16;
                            2'b11 : fpu_ifmt_d = IFMT_INT8;
                        endcase
                    // Scalar casts encoded in imm
                    end else begin
                        fpu_op_mod_d = operand_c_i[0];
                        if (operand_c_i[1])
                            fpu_ifmt_d = IFMT_INT64;
                        else
                            fpu_ifmt_d = IFMT_INT32;
                    end
                end
                // Int to Float Cast - Op encoded in lowest two imm bits or rm
                FCVT_I2F  : begin
                    fpu_op_d = OP_I2F;
                    // Vectorial Ops encoded in R bit
                    if (fpu_vec_op_d) begin
                        fpu_op_mod_d      = fpu_rm_i[0];
                        vec_replication = 1'b0; // no replication, R bit used for op
                        unique case (fpu_fmt_i)
                            2'b00 : fpu_ifmt_d = IFMT_INT32;
                            2'b01,
                            2'b10 : fpu_ifmt_d = IFMT_INT16;
                            2'b11 : fpu_ifmt_d = IFMT_INT8;
                        endcase
                    // Scalar casts encoded in imm
                    end else begin
                        fpu_op_mod_d = operand_c_i[0];
                        if (operand_c_i[1])
                            fpu_ifmt_d = IFMT_INT64;
                        else
                            fpu_ifmt_d = IFMT_INT32;
                    end
                end
                // Float to Float Cast - Source format encoded in lowest two/three imm bits
                FCVT_F2F  : begin
                    fpu_op_d = OP_F2F;
                    // Vectorial ops encoded in lowest two imm bits
                    if (fpu_vec_op_d) begin
                        vec_replication = 1'b0; // no replication for casts (not needed)
                        unique case (operand_c_i[1:0])
                            2'b00: fpu_fmt2_d = FMT_FP32;
                            2'b01: fpu_fmt2_d = FMT_FP16ALT;
                            2'b10: fpu_fmt2_d = FMT_FP16;
                            2'b11: fpu_fmt2_d = FMT_FP8;
                        endcase
                    // Scalar ops encoded in lowest three imm bits
                    end else begin
                        unique case (operand_c_i[2:0])
                            3'b000: fpu_fmt2_d = FMT_FP32;
                            3'b001: fpu_fmt2_d = FMT_FP64;
                            3'b010: fpu_fmt2_d = FMT_FP16;
                            3'b110: fpu_fmt2_d = FMT_FP16ALT;
                            3'b011: fpu_fmt2_d = FMT_FP8;
                        endcase
                    end
                end
                // Scalar Sign Injection - op encoded in rm (000-010)
                FSGNJ     : begin
                    fpu_op_d    = OP_SGNJ;
                    fpu_rm_d = {1'b0, fpu_rm_i[1:0]}; // mask out AH encoding bit
                    check_ah = 1'b1; // AH has RM MSB encoding
                end
                // Move from FPR to GPR - mapped to SGNJ-passthrough since no recoding
                FMV_F2X   : begin
                    fpu_op_d          = OP_SGNJ;
                    fpu_rm_d          = 3'b011; // passthrough without checking nan-box
                    fpu_op_mod_d      = 1'b1; // no NaN-Boxing
                    check_ah          = 1'b1; // AH has RM MSB encoding
                    vec_replication   = 1'b0; // no replication, we set second operand
                end
                // Move from GPR to FPR - mapped to NOP since no recoding
                FMV_X2F   : begin
                    fpu_op_d          = OP_SGNJ;
                    fpu_rm_d          = 3'b011; // passthrough without checking nan-box
                    check_ah          = 1'b1; // AH has RM MSB encoding
                    vec_replication   = 1'b0; // no replication, we set second operand
                end
                // Scalar Comparisons - op encoded in rm (000-010)
                FCMP      : begin
                    fpu_op_d = OP_CMP;
                    fpu_rm_d = {1'b0, fpu_rm_i[1:0]}; // mask out AH encoding bit
                    check_ah = 1'b1; // AH has RM MSB encoding
                end
                // Classification
                FCLASS    : begin
                    fpu_op_d = OP_CLASS;
                    fpu_rm_d = {1'b0, fpu_rm_i[1:0]}; // mask out AH encoding bit - CLASS doesn't care anyways
                    check_ah = 1'b1; // AH has RM MSB encoding
                end
                // Vectorial Minimum - set up scalar encoding in rm
                VFMIN     : begin
                    fpu_op_d = OP_MINMAX;
                    fpu_rm_d = 3'b000; // min
                end
                // Vectorial Maximum - set up scalar encoding in rm
                VFMAX     : begin
                    fpu_op_d = OP_MINMAX;
                    fpu_rm_d = 3'b001; // max
                end
                // Vectorial Sign Injection - set up scalar encoding in rm
                VFSGNJ    : begin
                    fpu_op_d = OP_SGNJ;
                    fpu_rm_d = 3'b000; // sgnj
                end
                // Vectorial Negated Sign Injection - set up scalar encoding in rm
                VFSGNJN   : begin
                    fpu_op_d = OP_SGNJ;
                    fpu_rm_d = 3'b001; // sgnjn
                end
                // Vectorial Xored Sign Injection - set up scalar encoding in rm
                VFSGNJX   : begin
                    fpu_op_d = OP_SGNJ;
                    fpu_rm_d = 3'b010; // sgnjx
                end
                // Vectorial Equals - set up scalar encoding in rm
                VFEQ      : begin
                    fpu_op_d = OP_CMP;
                    fpu_rm_d = 3'b010; // eq
                end
                // Vectorial Not Equals - set up scalar encoding in rm
                VFNE      : begin
                    fpu_op_d     = OP_CMP;
                    fpu_op_mod_d = 1'b1;   // invert output
                    fpu_rm_d     = 3'b010; // eq
                    end
                // Vectorial Less Than - set up scalar encoding in rm
                VFLT      : begin
                    fpu_op_d = OP_CMP;
                    fpu_rm_d = 3'b001; // lt
                end
                // Vectorial Greater or Equal - set up scalar encoding in rm
                VFGE      : begin
                    fpu_op_d     = OP_CMP;
                    fpu_op_mod_d = 1'b1;   // invert output
                    fpu_rm_d     = 3'b001; // lt
                end
                // Vectorial Less or Equal - set up scalar encoding in rm
                VFLE      : begin
                    fpu_op_d = OP_CMP;
                    fpu_rm_d = 3'b000; // le
                end
                // Vectorial Greater Than - set up scalar encoding in rm
                VFGT      : begin
                    fpu_op_d     = OP_CMP;
                    fpu_op_mod_d = 1'b1;   // invert output
                    fpu_rm_d     = 3'b000; // le
                end
                // Vectorial Convert-and-Pack from FP32, lower 4 entries
                VFCPKAB_S : begin
                    fpu_op_d        = OP_CPKAB;
                    fpu_op_mod_d    = fpu_rm_i[0]; // A/B selection from R bit
                    vec_replication = 1'b0;        // no replication, R bit used for op
                    fpu_fmt2_d      = FMT_FP32;    // Cast from FP32
                end
                // Vectorial Convert-and-Pack from FP32, upper 4 entries
                VFCPKCD_S : begin
                    fpu_op_d        = OP_CPKCD;
                    fpu_op_mod_d    = fpu_rm_i[0]; // C/D selection from R bit
                    vec_replication = 1'b0;        // no replication, R bit used for op
                    fpu_fmt2_d      = FMT_FP64;    // Cast from FP64
                end
                // Vectorial Convert-and-Pack from FP64, lower 4 entries
                VFCPKAB_S : begin
                    fpu_op_d        = OP_CPKAB;
                    fpu_op_mod_d    = fpu_rm_i[0]; // A/B selection from R bit
                    vec_replication = 1'b0;        // no replication, R bit used for op
                    fpu_fmt2_d      = FMT_FP64;    // Cast from FP64
                end
                // Vectorial Convert-and-Pack from FP64, upper 4 entries
                VFCPKCD_S : begin
                    fpu_op_d        = OP_CPKCD;
                    fpu_op_mod_d    = fpu_rm_i[0]; // C/D selection from R bit
                    vec_replication = 1'b0;        // no replication, R bit used for op
                    fpu_fmt2_d      = FMT_FP64;    // Cast from FP64
                end

                // No changes per default
                default : ; //nothing
            endcase

            // Scalar AH encoding fixing
            if (!fpu_vec_op_d && check_ah)
                if (fpu_rm_i[2])
                    fpu_fmt_d = FMT_FP16ALT;

            // Replication
            if (fpu_vec_op_d && vec_replication) begin
                if (replicate_c) begin
                    unique case (fpu_fmt_d)
                        FMT_FP32    : operand_c_d = RVD ? {2{operand_c_i[31:0]}} : operand_c_i;
                        FMT_FP16,
                        FMT_FP16ALT : operand_c_d = RVD ? {4{operand_c_i[15:0]}} : {2{operand_c_i[15:0]}};
                        FMT_FP8     : operand_c_d = RVD ? {8{operand_c_i[7:0]}}  : {4{operand_c_i[7:0]}};
                    endcase // fpu_fmt_d
                end else begin
                    unique case (fpu_fmt_d)
                        FMT_FP32    : operand_b_d = RVD ? {2{operand_b_i[31:0]}} : operand_b_i;
                        FMT_FP16,
                        FMT_FP16ALT : operand_b_d = RVD ? {4{operand_b_i[15:0]}} : {2{operand_b_i[15:0]}};
                        FMT_FP8     : operand_b_d = RVD ? {8{operand_b_i[7:0]}}  : {4{operand_b_i[7:0]}};
                    endcase // fpu_fmt_d
                end
            end
        end


        //---------------------------------------------------------
        // Upstream protocol inversion: InValid depends on InReady
        //---------------------------------------------------------

        always_comb begin : p_inputFSM
            // Default Values
            fpu_ready_o  = 1'b0;
            fpu_in_valid = 1'b0;
            hold_inputs = 1'b0;    // hold register disabled
            use_hold    = 1'b0;    // inputs go directly to unit
            state_d     = state_q; // stay in the same state

            // FSM
            unique case (state_q)
                // Default state, ready for instructions
                READY : begin
                    fpu_ready_o  = 1'b1;        // Act as if FPU ready
                    fpu_in_valid = fpu_valid_i; // Forward input valid to FPU
                    // There is a transaction but the FPU can't handle it
                    if (fpu_valid_i & ~fpu_in_ready) begin
                        fpu_ready_o = 1'b0;  // No token given to Issue
                        hold_inputs = 1'b1;  // save inputs to the holding register
                        state_d     = STALL; // stall future incoming requests
                    end
                end
                // We're stalling the upstream (ready=0)
                STALL : begin
                    fpu_in_valid = 1'b1; // we have data for the FPU
                    use_hold     = 1'b1; // the data comes from the hold reg
                    // Wait until it's consumed
                    if (fpu_in_ready) begin
                        fpu_ready_o = 1'b1;  // Give a token to issue
                        state_d     = READY; // accept future requests
                    end
                end
                // Default: emit default values
                default : ;
            endcase

            // Flushing will override issue and go back to idle
            if (flush_i) begin
                state_d      = READY;
            end

        end

        // Buffer register and FSM state holding
        always_ff @(posedge clk_i or negedge rst_ni) begin : fp_hold_reg
            if(~rst_ni) begin
                state_q       <= READY;
                operand_a_q   <= '0;
                operand_b_q   <= '0;
                operand_c_q   <= '0;
                fpu_op_q      <= '0;
                fpu_op_mod_q  <= '0;
                fpu_fmt_q     <= '0;
                fpu_fmt2_q    <= '0;
                fpu_ifmt_q    <= '0;
                fpu_rm_q      <= '0;
                fpu_vec_op_q  <= '0;
                fpu_tag_q     <= '0;
            end else begin
                state_q       <= state_d;
                // Hold register is [TRIGGERED] by FSM
                if (hold_inputs) begin
                    operand_a_q   <= operand_a_d;
                    operand_b_q   <= operand_b_d;
                    operand_c_q   <= operand_c_d;
                    fpu_op_q      <= fpu_op_d;
                    fpu_op_mod_q  <= fpu_op_mod_d;
                    fpu_fmt_q     <= fpu_fmt_d;
                    fpu_fmt2_q    <= fpu_fmt2_d;
                    fpu_ifmt_q    <= fpu_ifmt_d;
                    fpu_rm_q      <= fpu_rm_d;
                    fpu_vec_op_q  <= fpu_vec_op_d;
                    fpu_tag_q     <= fpu_tag_d;
                end
            end
        end

        // Select FPU input data: from register if valid data in register, else directly from input
        assign operand_a  = use_hold ? operand_a_q  : operand_a_d;
        assign operand_b  = use_hold ? operand_b_q  : operand_b_d;
        assign operand_c  = use_hold ? operand_c_q  : operand_c_d;
        assign fpu_op     = use_hold ? fpu_op_q     : fpu_op_d;
        assign fpu_op_mod = use_hold ? fpu_op_mod_q : fpu_op_mod_d;
        assign fpu_fmt    = use_hold ? fpu_fmt_q    : fpu_fmt_d;
        assign fpu_fmt2   = use_hold ? fpu_fmt2_q   : fpu_fmt2_d;
        assign fpu_ifmt   = use_hold ? fpu_ifmt_q   : fpu_ifmt_d;
        assign fpu_rm     = use_hold ? fpu_rm_q     : fpu_rm_d;
        assign fpu_vec_op = use_hold ? fpu_vec_op_q : fpu_vec_op_d;
        assign fpu_tag    = use_hold ? fpu_tag_q    : fpu_tag_d;

        //---------------
        // FPU instance
        //---------------
        fpnew_top #(
            .WIDTH                ( FLEN          ),
            .TAG_WIDTH            ( TRANS_ID_BITS ),
            .RV64                 ( 1'b1          ),
            .RVF                  ( RVF           ),
            .RVD                  ( RVD           ),
            .Xf16                 ( XF16          ),
            .Xf16alt              ( XF16ALT       ),
            .Xf8                  ( XF8           ),
            .Xfvec                ( XFVEC         ),
            // TODO MOVE THESE VALUES TO PACKAGE
            .LATENCY_COMP_F       ( LAT_COMP_FP32    ),
            .LATENCY_COMP_D       ( LAT_COMP_FP64    ),
            .LATENCY_COMP_Xf16    ( LAT_COMP_FP16    ),
            .LATENCY_COMP_Xf16alt ( LAT_COMP_FP16ALT ),
            .LATENCY_COMP_Xf8     ( LAT_COMP_FP8     ),
            .LATENCY_DIVSQRT      ( LAT_DIVSQRT      ),
            .LATENCY_NONCOMP      ( LAT_NONCOMP      ),
            .LATENCY_CONV         ( LAT_CONV         )
        ) fpnew_top_i (
            .Clk_CI         ( clk_i          ),
            .Reset_RBI      ( rst_ni         ),
            .A_DI           ( operand_a      ),
            .B_DI           ( operand_b      ),
            .C_DI           ( operand_c      ),
            .RoundMode_SI   ( fpu_rm         ),
            .Op_SI          ( fpu_op         ),
            .OpMod_SI       ( fpu_op_mod     ),
            .VectorialOp_SI ( fpu_vec_op     ),
            .FpFmt_SI       ( fpu_fmt        ),
            .FpFmt2_SI      ( fpu_fmt2       ),
            .IntFmt_SI      ( fpu_ifmt       ),
            .Tag_DI         ( fpu_tag        ),
            .PrecCtl_SI     ( fpu_prec_i     ),
            .InValid_SI     ( fpu_in_valid   ),
            .InReady_SO     ( fpu_in_ready   ),
            .Flush_SI       ( flush_i        ),
            .Z_DO           ( result_o       ),
            .Status_DO      ( fpu_status     ),
            .Tag_DO         ( fpu_trans_id_o ),
            .OutValid_SO    ( fpu_out_valid  ),
            .OutReady_SI    ( fpu_out_ready  )
        );

        // Pack status flag into exception cause, tval ignored in wb, exception is always invalid
        assign fpu_exception_o.cause = {59'h0, fpu_status};
        assign fpu_exception_o.valid = 1'b0;

        // Donwstream write port is dedicated to FPU and always ready
        assign fpu_out_ready = 1'b1;

        // Downstream valid from unit
        assign fpu_valid_o = fpu_out_valid;

    end
endgenerate
endmodule
