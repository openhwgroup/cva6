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
// File:   issue_read_operands.sv
// Author: Florian Zaruba <zarubaf@ethz.ch>
// Date:   8.4.2017
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// Description: Issues instruction from the scoreboard and fetches the operands
//              This also includes all the forwarding logic
//

module decoder import ariane_pkg::*; (
    input  logic               debug_req_i,             // external debug request
    input  logic [riscv::VLEN-1:0] pc_i,                // PC from IF
    input  logic               is_compressed_i,         // is a compressed instruction
    input  logic [15:0]        compressed_instr_i,      // compressed form of instruction
    input  logic               is_illegal_i,            // illegal compressed instruction
    input  logic [31:0]        instruction_i,           // instruction from IF
    input  branchpredict_sbe_t branch_predict_i,
    input  exception_t         ex_i,                    // if an exception occured in if
    input  logic [1:0]         irq_i,                   // external interrupt
    input  irq_ctrl_t          irq_ctrl_i,              // interrupt control and status information from CSRs
    // From CSR
    input  riscv::priv_lvl_t   priv_lvl_i,              // current privilege level
    input  logic               debug_mode_i,            // we are in debug mode
    input  riscv::xs_t         fs_i,                    // floating point extension status
    input  logic [2:0]         frm_i,                   // floating-point dynamic rounding mode
    input  logic               tvm_i,                   // trap virtual memory
    input  logic               tw_i,                    // timeout wait
    input  logic               tsr_i,                   // trap sret
    output scoreboard_entry_t  instruction_o,           // scoreboard entry to scoreboard
    output logic               is_control_flow_instr_o  // this instruction will change the control flow
);
    logic illegal_instr;
    // this instruction is an environment call (ecall), it is handled like an exception
    logic ecall;
    // this instruction is a software break-point
    logic ebreak;
    // this instruction needs floating-point rounding-mode verification
    logic check_fprm;
    riscv::instruction_t instr;
    assign instr = riscv::instruction_t'(instruction_i);
    // --------------------
    // Immediate select
    // --------------------
    enum logic[3:0] {
        NOIMM, IIMM, SIMM, SBIMM, UIMM, JIMM, RS3
    } imm_select;

    riscv::xlen_t imm_i_type;
    riscv::xlen_t imm_s_type;
    riscv::xlen_t imm_sb_type;
    riscv::xlen_t imm_u_type;
    riscv::xlen_t imm_uj_type;
    riscv::xlen_t imm_bi_type;

    always_comb begin : decoder

        imm_select                  = NOIMM;
        is_control_flow_instr_o     = 1'b0;
        illegal_instr               = 1'b0;
        instruction_o.pc            = pc_i;
        instruction_o.trans_id      = 5'b0;
        instruction_o.fu            = NONE;
        instruction_o.op            = ariane_pkg::ADD;
        instruction_o.rs1           = '0;
        instruction_o.rs2           = '0;
        instruction_o.rd            = '0;
        instruction_o.use_pc        = 1'b0;
        instruction_o.trans_id      = '0;
        instruction_o.is_compressed = is_compressed_i;
        instruction_o.use_zimm      = 1'b0;
        instruction_o.bp            = branch_predict_i;
        ecall                       = 1'b0;
        ebreak                      = 1'b0;
        check_fprm                  = 1'b0;

        if (~ex_i.valid) begin
            case (instr.rtype.opcode)
                riscv::OpcodeSystem: begin
                    instruction_o.fu       = CSR;
                    instruction_o.rs1[4:0] = instr.itype.rs1;
                    instruction_o.rs2[4:0] = instr.rtype.rs2;   //TODO: needs to be checked if better way is available
                    instruction_o.rd[4:0]  = instr.itype.rd;

                    unique case (instr.itype.funct3)
                        3'b000: begin
                            // check if the RD and and RS1 fields are zero, this may be reset for the SENCE.VMA instruction
                            if (instr.itype.rs1 != '0 || instr.itype.rd != '0)
                                illegal_instr = 1'b1;
                            // decode the immiediate field
                            case (instr.itype.imm)
                                // ECALL -> inject exception
                                12'b0: ecall  = 1'b1;
                                // EBREAK -> inject exception
                                12'b1: ebreak = 1'b1;
                                // SRET
                                12'b1_0000_0010: begin
                                    instruction_o.op = ariane_pkg::SRET;
                                    // check privilege level, SRET can only be executed in S and M mode
                                    // we'll just decode an illegal instruction if we are in the wrong privilege level
                                    if (priv_lvl_i == riscv::PRIV_LVL_U) begin
                                        illegal_instr = 1'b1;
                                        //  do not change privilege level if this is an illegal instruction
                                        instruction_o.op = ariane_pkg::ADD;
                                    end
                                    // if we are in S-Mode and Trap SRET (tsr) is set -> trap on illegal instruction
                                    if (priv_lvl_i == riscv::PRIV_LVL_S && tsr_i) begin
                                        illegal_instr = 1'b1;
                                        //  do not change privilege level if this is an illegal instruction
                                        instruction_o.op = ariane_pkg::ADD;
                                    end
                                end
                                // MRET
                                12'b11_0000_0010: begin
                                    instruction_o.op = ariane_pkg::MRET;
                                    // check privilege level, MRET can only be executed in M mode
                                    // otherwise we decode an illegal instruction
                                    if (priv_lvl_i inside {riscv::PRIV_LVL_U, riscv::PRIV_LVL_S})
                                        illegal_instr = 1'b1;
                                end
                                // DRET
                                12'b111_1011_0010: begin
                                    instruction_o.op = ariane_pkg::DRET;
                                    // check that we are in debug mode when executing this instruction
                                    illegal_instr = (!debug_mode_i) ? 1'b1 : 1'b0;
                                end
                                // WFI
                                12'b1_0000_0101: begin
                                    if (ENABLE_WFI) instruction_o.op = ariane_pkg::WFI;
                                    // if timeout wait is set, trap on an illegal instruction in S Mode
                                    // (after 0 cycles timeout)
                                    if (priv_lvl_i == riscv::PRIV_LVL_S && tw_i) begin
                                        illegal_instr = 1'b1;
                                        instruction_o.op = ariane_pkg::ADD;
                                    end
                                    // we don't support U mode interrupts so WFI is illegal in this context
                                    if (priv_lvl_i == riscv::PRIV_LVL_U) begin
                                        illegal_instr = 1'b1;
                                        instruction_o.op = ariane_pkg::ADD;
                                    end
                                end
                                // SFENCE.VMA
                                default: begin
                                    if (instr.instr[31:25] == 7'b1001) begin
                                        // check privilege level, SFENCE.VMA can only be executed in M/S mode
                                        // otherwise decode an illegal instruction
                                        illegal_instr    = (priv_lvl_i inside {riscv::PRIV_LVL_M, riscv::PRIV_LVL_S}) ? 1'b0 : 1'b1;
                                        instruction_o.op = ariane_pkg::SFENCE_VMA;
                                        // check TVM flag and intercept SFENCE.VMA call if necessary
                                        if (priv_lvl_i == riscv::PRIV_LVL_S && tvm_i)
                                            illegal_instr = 1'b1;
                                    end
                                end
                            endcase
                        end
                        // atomically swaps values in the CSR and integer register
                        3'b001: begin// CSRRW
                            imm_select = IIMM;
                            instruction_o.op = ariane_pkg::CSR_WRITE;
                        end
                        // atomically set values in the CSR and write back to rd
                        3'b010: begin// CSRRS
                            imm_select = IIMM;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = ariane_pkg::CSR_READ;
                            else
                                instruction_o.op = ariane_pkg::CSR_SET;
                        end
                        // atomically clear values in the CSR and write back to rd
                        3'b011: begin// CSRRC
                            imm_select = IIMM;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = ariane_pkg::CSR_READ;
                            else
                                instruction_o.op = ariane_pkg::CSR_CLEAR;
                        end
                        // use zimm and iimm
                        3'b101: begin// CSRRWI
                            instruction_o.rs1[4:0] = instr.itype.rs1;
                            imm_select = IIMM;
                            instruction_o.use_zimm = 1'b1;
                            instruction_o.op = ariane_pkg::CSR_WRITE;
                        end
                        3'b110: begin// CSRRSI
                            instruction_o.rs1[4:0] = instr.itype.rs1;
                            imm_select = IIMM;
                            instruction_o.use_zimm = 1'b1;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = ariane_pkg::CSR_READ;
                            else
                                instruction_o.op = ariane_pkg::CSR_SET;
                        end
                        3'b111: begin// CSRRCI
                            instruction_o.rs1[4:0] = instr.itype.rs1;
                            imm_select = IIMM;
                            instruction_o.use_zimm = 1'b1;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = ariane_pkg::CSR_READ;
                            else
                                instruction_o.op = ariane_pkg::CSR_CLEAR;
                        end
                        default: illegal_instr = 1'b1;
                    endcase
                end
                // Memory ordering instructions
                riscv::OpcodeMiscMem: begin
                    instruction_o.fu  = CSR;
                    instruction_o.rs1 = '0;
                    instruction_o.rs2 = '0;
                    instruction_o.rd  = '0;

                    case (instr.stype.funct3)
                        // FENCE
                        // Currently implemented as a whole DCache flush boldly ignoring other things
                        3'b000: instruction_o.op  = ariane_pkg::FENCE;
                        // FENCE.I
                        3'b001: begin
                            if (instr.instr[31:20] != '0)
                                illegal_instr = 1'b1;
                            instruction_o.op  = ariane_pkg::FENCE_I;
                        end
                        default: illegal_instr = 1'b1;
                    endcase

                    if (instr.stype.rs1 != '0 || instr.stype.imm0 != '0 || instr.instr[31:28] != '0)
                        illegal_instr = 1'b1;
                end

                // --------------------------
                // Reg-Reg Operations
                // --------------------------
                riscv::OpcodeOp: begin
                    // --------------------------------------------
                    // Vectorial Floating-Point Reg-Reg Operations
                    // --------------------------------------------
                    if (instr.rvftype.funct2 == 2'b10) begin // Prefix 10 for all Xfvec ops
                        // only generate decoder if FP extensions are enabled (static)
                        if (FP_PRESENT && XFVEC && fs_i != riscv::Off) begin
                            automatic logic allow_replication; // control honoring of replication flag

                            instruction_o.fu       = FPU_VEC; // Same unit, but sets 'vectorial' signal
                            instruction_o.rs1[4:0] = instr.rvftype.rs1;
                            instruction_o.rs2[4:0] = instr.rvftype.rs2;
                            instruction_o.rd[4:0]  = instr.rvftype.rd;
                            check_fprm             = 1'b1;
                            allow_replication      = 1'b1;
                            // decode vectorial FP instruction
                            unique case (instr.rvftype.vecfltop)
                                5'b00001 : begin
                                    instruction_o.op  = ariane_pkg::FADD; // vfadd.vfmt - Vectorial FP Addition
                                    instruction_o.rs1 = '0;                // Operand A is set to 0
                                    instruction_o.rs2 = instr.rvftype.rs1; // Operand B is set to rs1
                                    imm_select        = IIMM;              // Operand C is set to rs2
                                end
                                5'b00010 : begin
                                    instruction_o.op  = ariane_pkg::FSUB; // vfsub.vfmt - Vectorial FP Subtraction
                                    instruction_o.rs1 = '0;                // Operand A is set to 0
                                    instruction_o.rs2 = instr.rvftype.rs1; // Operand B is set to rs1
                                    imm_select        = IIMM;              // Operand C is set to rs2
                                end
                                5'b00011 : instruction_o.op = ariane_pkg::FMUL; // vfmul.vfmt - Vectorial FP Multiplication
                                5'b00100 : instruction_o.op = ariane_pkg::FDIV; // vfdiv.vfmt - Vectorial FP Division
                                5'b00101 : begin
                                    instruction_o.op = ariane_pkg::VFMIN; // vfmin.vfmt - Vectorial FP Minimum
                                    check_fprm       = 1'b0;  // rounding mode irrelevant
                                end
                                5'b00110 : begin
                                    instruction_o.op = ariane_pkg::VFMAX; // vfmax.vfmt - Vectorial FP Maximum
                                    check_fprm       = 1'b0;  // rounding mode irrelevant
                                end
                                5'b00111 : begin
                                    instruction_o.op  = ariane_pkg::FSQRT; // vfsqrt.vfmt - Vectorial FP Square Root
                                    allow_replication = 1'b0;  // only one operand
                                    if (instr.rvftype.rs2 != 5'b00000) illegal_instr = 1'b1; // rs2 must be 0
                                end
                                5'b01000 : begin
                                    instruction_o.op = ariane_pkg::FMADD; // vfmac.vfmt - Vectorial FP Multiply-Accumulate
                                    imm_select       = SIMM;  // rd into result field (upper bits don't matter)
                                end
                                5'b01001 : begin
                                    instruction_o.op = ariane_pkg::FMSUB; // vfmre.vfmt - Vectorial FP Multiply-Reduce
                                    imm_select       = SIMM;  // rd into result field (upper bits don't matter)
                                end
                                5'b01100 : begin
                                    unique case (instr.rvftype.rs2) inside // operation encoded in rs2, `inside` for matching ?
                                        5'b00000 : begin
                                            instruction_o.rs2 = instr.rvftype.rs1; // set rs2 = rs1 so we can map FMV to SGNJ in the unit
                                            if (instr.rvftype.repl)
                                                instruction_o.op = ariane_pkg::FMV_X2F; // vfmv.vfmt.x - GPR to FPR Move
                                            else
                                                instruction_o.op = ariane_pkg::FMV_F2X; // vfmv.x.vfmt - FPR to GPR Move
                                            check_fprm = 1'b0;              // no rounding for moves
                                        end
                                        5'b00001 : begin
                                            instruction_o.op  = ariane_pkg::FCLASS; // vfclass.vfmt - Vectorial FP Classify
                                            check_fprm        = 1'b0;   // no rounding for classification
                                            allow_replication = 1'b0;   // R must not be set
                                        end
                                        5'b00010 : instruction_o.op = ariane_pkg::FCVT_F2I; // vfcvt.x.vfmt - Vectorial FP to Int Conversion
                                        5'b00011 : instruction_o.op = ariane_pkg::FCVT_I2F; // vfcvt.vfmt.x - Vectorial Int to FP Conversion
                                        5'b001?? : begin
                                            instruction_o.op  = ariane_pkg::FCVT_F2F; // vfcvt.vfmt.vfmt - Vectorial FP to FP Conversion
                                            instruction_o.rs2 = instr.rvftype.rd; // set rs2 = rd as target vector for conversion
                                            imm_select        = IIMM;     // rs2 holds part of the intruction
                                            // TODO CHECK R bit for valid fmt combinations
                                            // determine source format
                                            unique case (instr.rvftype.rs2[21:20])
                                                // Only process instruction if corresponding extension is active (static)
                                                2'b00: if (~RVFVEC)     illegal_instr = 1'b1;
                                                2'b01: if (~XF16ALTVEC) illegal_instr = 1'b1;
                                                2'b10: if (~XF16VEC)    illegal_instr = 1'b1;
                                                2'b11: if (~XF8VEC)     illegal_instr = 1'b1;
                                                default : illegal_instr = 1'b1;
                                            endcase
                                        end
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                5'b01101 : begin
                                    check_fprm = 1'b0;         // no rounding for sign-injection
                                    instruction_o.op = ariane_pkg::VFSGNJ; // vfsgnj.vfmt - Vectorial FP Sign Injection
                                end
                                5'b01110 : begin
                                    check_fprm = 1'b0;          // no rounding for sign-injection
                                    instruction_o.op = ariane_pkg::VFSGNJN; // vfsgnjn.vfmt - Vectorial FP Negated Sign Injection
                                end
                                5'b01111 : begin
                                    check_fprm = 1'b0;          // no rounding for sign-injection
                                    instruction_o.op = ariane_pkg::VFSGNJX; // vfsgnjx.vfmt - Vectorial FP XORed Sign Injection
                                end
                                5'b10000 : begin
                                    check_fprm = 1'b0;          // no rounding for comparisons
                                    instruction_o.op = ariane_pkg::VFEQ;    // vfeq.vfmt - Vectorial FP Equality
                                end
                                5'b10001 : begin
                                    check_fprm = 1'b0;          // no rounding for comparisons
                                    instruction_o.op = ariane_pkg::VFNE;    // vfne.vfmt - Vectorial FP Non-Equality
                                end
                                5'b10010 : begin
                                    check_fprm = 1'b0;          // no rounding for comparisons
                                    instruction_o.op = ariane_pkg::VFLT;    // vfle.vfmt - Vectorial FP Less Than
                                end
                                5'b10011 : begin
                                    check_fprm = 1'b0;          // no rounding for comparisons
                                    instruction_o.op = ariane_pkg::VFGE;    // vfge.vfmt - Vectorial FP Greater or Equal
                                end
                                5'b10100 : begin
                                    check_fprm = 1'b0;          // no rounding for comparisons
                                    instruction_o.op = ariane_pkg::VFLE;    // vfle.vfmt - Vectorial FP Less or Equal
                                end
                                5'b10101 : begin
                                    check_fprm = 1'b0;          // no rounding for comparisons
                                    instruction_o.op = ariane_pkg::VFGT;    // vfgt.vfmt - Vectorial FP Greater Than
                                end
                                5'b11000 : begin
                                    instruction_o.op  = ariane_pkg::VFCPKAB_S; // vfcpka/b.vfmt.s - Vectorial FP Cast-and-Pack from 2x FP32, lowest 4 entries
                                    imm_select        = SIMM;      // rd into result field (upper bits don't matter)
                                    if (~RVF) illegal_instr = 1'b1; // if we don't support RVF, we can't cast from FP32
                                    // check destination format
                                    unique case (instr.rvftype.vfmt)
                                        // Only process instruction if corresponding extension is active and FLEN suffices (static)
                                        2'b00: begin
                                            if (~RVFVEC)            illegal_instr = 1'b1; // destination vector not supported
                                            if (instr.rvftype.repl) illegal_instr = 1'b1; // no entries 2/3 in vector of 2 fp32
                                        end
                                        2'b01: begin
                                            if (~XF16ALTVEC) illegal_instr = 1'b1; // destination vector not supported
                                        end
                                        2'b10: begin
                                            if (~XF16VEC) illegal_instr = 1'b1; // destination vector not supported
                                        end
                                        2'b11: begin
                                            if (~XF8VEC) illegal_instr = 1'b1; // destination vector not supported
                                        end
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                5'b11001 : begin
                                    instruction_o.op  = ariane_pkg::VFCPKCD_S; // vfcpkc/d.vfmt.s - Vectorial FP Cast-and-Pack from 2x FP32, second 4 entries
                                    imm_select        = SIMM;      // rd into result field (upper bits don't matter)
                                    if (~RVF) illegal_instr = 1'b1; // if we don't support RVF, we can't cast from FP32
                                    // check destination format
                                    unique case (instr.rvftype.vfmt)
                                        // Only process instruction if corresponding extension is active and FLEN suffices (static)
                                        2'b00: illegal_instr = 1'b1; // no entries 4-7 in vector of 2 FP32
                                        2'b01: illegal_instr = 1'b1; // no entries 4-7 in vector of 4 FP16ALT
                                        2'b10: illegal_instr = 1'b1; // no entries 4-7 in vector of 4 FP16
                                        2'b11: begin
                                            if (~XF8VEC) illegal_instr = 1'b1; // destination vector not supported
                                        end
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                5'b11010 : begin
                                    instruction_o.op  = ariane_pkg::VFCPKAB_D; // vfcpka/b.vfmt.d - Vectorial FP Cast-and-Pack from 2x FP64, lowest 4 entries
                                    imm_select        = SIMM;      // rd into result field (upper bits don't matter)
                                    if (~RVD) illegal_instr = 1'b1; // if we don't support RVD, we can't cast from FP64
                                    // check destination format
                                    unique case (instr.rvftype.vfmt)
                                        // Only process instruction if corresponding extension is active and FLEN suffices (static)
                                        2'b00: begin
                                            if (~RVFVEC)            illegal_instr = 1'b1; // destination vector not supported
                                            if (instr.rvftype.repl) illegal_instr = 1'b1; // no entries 2/3 in vector of 2 fp32
                                        end
                                        2'b01: begin
                                            if (~XF16ALTVEC) illegal_instr = 1'b1; // destination vector not supported
                                        end
                                        2'b10: begin
                                            if (~XF16VEC) illegal_instr = 1'b1; // destination vector not supported
                                        end
                                        2'b11: begin
                                            if (~XF8VEC) illegal_instr = 1'b1; // destination vector not supported
                                        end
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                5'b11011 : begin
                                    instruction_o.op  = ariane_pkg::VFCPKCD_D; // vfcpka/b.vfmt.d - Vectorial FP Cast-and-Pack from 2x FP64, second 4 entries
                                    imm_select        = SIMM;      // rd into result field (upper bits don't matter)
                                    if (~RVD) illegal_instr = 1'b1; // if we don't support RVD, we can't cast from FP64
                                    // check destination format
                                    unique case (instr.rvftype.vfmt)
                                        // Only process instruction if corresponding extension is active and FLEN suffices (static)
                                        2'b00: illegal_instr = 1'b1; // no entries 4-7 in vector of 2 FP32
                                        2'b01: illegal_instr = 1'b1; // no entries 4-7 in vector of 4 FP16ALT
                                        2'b10: illegal_instr = 1'b1; // no entries 4-7 in vector of 4 FP16
                                        2'b11: begin
                                            if (~XF8VEC) illegal_instr = 1'b1; // destination vector not supported
                                        end
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                default : illegal_instr = 1'b1;
                            endcase

                            // check format
                            unique case (instr.rvftype.vfmt)
                                // Only process instruction if corresponding extension is active (static)
                                2'b00: if (~RVFVEC)     illegal_instr = 1'b1;
                                2'b01: if (~XF16ALTVEC) illegal_instr = 1'b1;
                                2'b10: if (~XF16VEC)    illegal_instr = 1'b1;
                                2'b11: if (~XF8VEC)     illegal_instr = 1'b1;
                                default: illegal_instr = 1'b1;
                            endcase

                            // check disallowed replication
                            if (~allow_replication & instr.rvftype.repl) illegal_instr = 1'b1;

                            // check rounding mode
                            if (check_fprm) begin
                                unique case (frm_i) inside // actual rounding mode from frm csr
                                    [3'b000:3'b100]: ; //legal rounding modes
                                    default : illegal_instr = 1'b1;
                                endcase
                            end

                        end else begin // No vectorial FP enabled (static)
                            illegal_instr = 1'b1;
                        end

                    // ---------------------------
                    // Integer Reg-Reg Operations
                    // ---------------------------
                    end else begin
                        instruction_o.fu  = (instr.rtype.funct7 == 7'b000_0001) ? MULT : ALU;
                        instruction_o.rs1 = instr.rtype.rs1;
                        instruction_o.rs2 = instr.rtype.rs2;
                        instruction_o.rd  = instr.rtype.rd;

                        unique case ({instr.rtype.funct7, instr.rtype.funct3})
                            {7'b000_0000, 3'b000}: instruction_o.op = ariane_pkg::ADD;   // Add
                            {7'b010_0000, 3'b000}: instruction_o.op = ariane_pkg::SUB;   // Sub
                            {7'b000_0000, 3'b010}: instruction_o.op = ariane_pkg::SLTS;  // Set Lower Than
                            {7'b000_0000, 3'b011}: instruction_o.op = ariane_pkg::SLTU;  // Set Lower Than Unsigned
                            {7'b000_0000, 3'b100}: instruction_o.op = ariane_pkg::XORL;  // Xor
                            {7'b000_0000, 3'b110}: instruction_o.op = ariane_pkg::ORL;   // Or
                            {7'b000_0000, 3'b111}: instruction_o.op = ariane_pkg::ANDL;  // And
                            {7'b000_0000, 3'b001}: instruction_o.op = ariane_pkg::SLL;   // Shift Left Logical
                            {7'b000_0000, 3'b101}: instruction_o.op = ariane_pkg::SRL;   // Shift Right Logical
                            {7'b010_0000, 3'b101}: instruction_o.op = ariane_pkg::SRA;   // Shift Right Arithmetic
                            // Multiplications
                            {7'b000_0001, 3'b000}: instruction_o.op = ariane_pkg::MUL;
                            {7'b000_0001, 3'b001}: instruction_o.op = ariane_pkg::MULH;
                            {7'b000_0001, 3'b010}: instruction_o.op = ariane_pkg::MULHSU;
                            {7'b000_0001, 3'b011}: instruction_o.op = ariane_pkg::MULHU;
                            {7'b000_0001, 3'b100}: instruction_o.op = ariane_pkg::DIV;
                            {7'b000_0001, 3'b101}: instruction_o.op = ariane_pkg::DIVU;
                            {7'b000_0001, 3'b110}: instruction_o.op = ariane_pkg::REM;
                            {7'b000_0001, 3'b111}: instruction_o.op = ariane_pkg::REMU;
                            default: begin
                                illegal_instr = 1'b1;
                            end
                        endcase
                    end
                end

                // --------------------------
                // 32bit Reg-Reg Operations
                // --------------------------
                riscv::OpcodeOp32: begin
                    instruction_o.fu  = (instr.rtype.funct7 == 7'b000_0001) ? MULT : ALU;
                    instruction_o.rs1[4:0] = instr.rtype.rs1;
                    instruction_o.rs2[4:0] = instr.rtype.rs2;
                    instruction_o.rd[4:0]  = instr.rtype.rd;
                      if (riscv::IS_XLEN64) begin
                        unique case ({instr.rtype.funct7, instr.rtype.funct3})
                            {7'b000_0000, 3'b000}: instruction_o.op = ariane_pkg::ADDW; // addw
                            {7'b010_0000, 3'b000}: instruction_o.op = ariane_pkg::SUBW; // subw
                            {7'b000_0000, 3'b001}: instruction_o.op = ariane_pkg::SLLW; // sllw
                            {7'b000_0000, 3'b101}: instruction_o.op = ariane_pkg::SRLW; // srlw
                            {7'b010_0000, 3'b101}: instruction_o.op = ariane_pkg::SRAW; // sraw
                            // Multiplications
                            {7'b000_0001, 3'b000}: instruction_o.op = ariane_pkg::MULW;
                            {7'b000_0001, 3'b100}: instruction_o.op = ariane_pkg::DIVW;
                            {7'b000_0001, 3'b101}: instruction_o.op = ariane_pkg::DIVUW;
                            {7'b000_0001, 3'b110}: instruction_o.op = ariane_pkg::REMW;
                            {7'b000_0001, 3'b111}: instruction_o.op = ariane_pkg::REMUW;
                            default: illegal_instr = 1'b1;
                        endcase
                      end else illegal_instr = 1'b1;
                end
                // --------------------------------
                // Reg-Immediate Operations
                // --------------------------------
                riscv::OpcodeOpImm: begin
                    instruction_o.fu  = ALU;
                    imm_select = IIMM;
                    instruction_o.rs1[4:0] = instr.itype.rs1;
                    instruction_o.rd[4:0]  = instr.itype.rd;

                    unique case (instr.itype.funct3)
                        3'b000: instruction_o.op = ariane_pkg::ADD;   // Add Immediate
                        3'b010: instruction_o.op = ariane_pkg::SLTS;  // Set to one if Lower Than Immediate
                        3'b011: instruction_o.op = ariane_pkg::SLTU;  // Set to one if Lower Than Immediate Unsigned
                        3'b100: instruction_o.op = ariane_pkg::XORL;  // Exclusive Or with Immediate
                        3'b110: instruction_o.op = ariane_pkg::ORL;   // Or with Immediate
                        3'b111: instruction_o.op = ariane_pkg::ANDL;  // And with Immediate

                        3'b001: begin
                          instruction_o.op = ariane_pkg::SLL;  // Shift Left Logical by Immediate
                          if (instr.instr[31:26] != 6'b0)
                            illegal_instr = 1'b1;
                          if (instr.instr[25] != 1'b0 && riscv::XLEN==32) illegal_instr = 1'b1;
                        end

                        3'b101: begin
                            if (instr.instr[31:26] == 6'b0)
                                instruction_o.op = ariane_pkg::SRL;  // Shift Right Logical by Immediate
                            else if (instr.instr[31:26] == 6'b010_000)
                                instruction_o.op = ariane_pkg::SRA;  // Shift Right Arithmetically by Immediate
                            else
                                illegal_instr = 1'b1;
                            if (instr.instr[25] != 1'b0 && riscv::XLEN==32) illegal_instr = 1'b1;
                        end
                    endcase
                end

                // --------------------------------
                // 32 bit Reg-Immediate Operations
                // --------------------------------
                riscv::OpcodeOpImm32: begin
                    instruction_o.fu  = ALU;
                    imm_select = IIMM;
                    instruction_o.rs1[4:0] = instr.itype.rs1;
                    instruction_o.rd[4:0]  = instr.itype.rd;
                    if (riscv::IS_XLEN64)
                    unique case (instr.itype.funct3)
                        3'b000: instruction_o.op = ariane_pkg::ADDW;  // Add Immediate

                        3'b001: begin
                          instruction_o.op = ariane_pkg::SLLW;  // Shift Left Logical by Immediate
                          if (instr.instr[31:25] != 7'b0)
                              illegal_instr = 1'b1;
                        end

                        3'b101: begin
                            if (instr.instr[31:25] == 7'b0)
                                instruction_o.op = ariane_pkg::SRLW;  // Shift Right Logical by Immediate
                            else if (instr.instr[31:25] == 7'b010_0000)
                                instruction_o.op = ariane_pkg::SRAW;  // Shift Right Arithmetically by Immediate
                            else
                                illegal_instr = 1'b1;
                        end

                        default: illegal_instr = 1'b1;
                    endcase
                    else illegal_instr = 1'b1;
                end
                // --------------------------------
                // LSU
                // --------------------------------
                riscv::OpcodeStore: begin
                    instruction_o.fu  = STORE;
                    imm_select = SIMM;
                    instruction_o.rs1[4:0]  = instr.stype.rs1;
                    instruction_o.rs2[4:0]  = instr.stype.rs2;
                    // determine store size
                    unique case (instr.stype.funct3)
                        3'b000: instruction_o.op  = ariane_pkg::SB;
                        3'b001: instruction_o.op  = ariane_pkg::SH;
                        3'b010: instruction_o.op  = ariane_pkg::SW;
                        3'b011: if (riscv::XLEN==64) instruction_o.op  = ariane_pkg::SD; 
                                else illegal_instr = 1'b1;
                        default: illegal_instr = 1'b1;
                    endcase
                end

                riscv::OpcodeLoad: begin
                    instruction_o.fu  = LOAD;
                    imm_select = IIMM;
                    instruction_o.rs1[4:0] = instr.itype.rs1;
                    instruction_o.rd[4:0]  = instr.itype.rd;
                    // determine load size and signed type
                    unique case (instr.itype.funct3)
                        3'b000: instruction_o.op  = ariane_pkg::LB;
                        3'b001: instruction_o.op  = ariane_pkg::LH;
                        3'b010: instruction_o.op  = ariane_pkg::LW;
                        3'b100: instruction_o.op  = ariane_pkg::LBU;
                        3'b101: instruction_o.op  = ariane_pkg::LHU;
                        3'b110: instruction_o.op  = ariane_pkg::LWU;
                        3'b011: if (riscv::XLEN==64) instruction_o.op  = ariane_pkg::LD; 
                                else illegal_instr = 1'b1;
                        default: illegal_instr = 1'b1;
                    endcase
                end

                // --------------------------------
                // Floating-Point Load/store
                // --------------------------------
                riscv::OpcodeStoreFp: begin
                    if (FP_PRESENT && fs_i != riscv::Off) begin // only generate decoder if FP extensions are enabled (static)
                        instruction_o.fu  = STORE;
                        imm_select = SIMM;
                        instruction_o.rs1        = instr.stype.rs1;
                        instruction_o.rs2        = instr.stype.rs2;
                        // determine store size
                        unique case (instr.stype.funct3)
                            // Only process instruction if corresponding extension is active (static)
                            3'b000: if (XF8) instruction_o.op = ariane_pkg::FSB;
                                    else illegal_instr = 1'b1;
                            3'b001: if (XF16 | XF16ALT) instruction_o.op = ariane_pkg::FSH;
                                    else illegal_instr = 1'b1;
                            3'b010: if (RVF) instruction_o.op = ariane_pkg::FSW;
                                    else illegal_instr = 1'b1;
                            3'b011: if (RVD) instruction_o.op = ariane_pkg::FSD;
                                    else illegal_instr = 1'b1;
                            default: illegal_instr = 1'b1;
                        endcase
                    end else
                        illegal_instr = 1'b1;
                end

                riscv::OpcodeLoadFp: begin
                    if (FP_PRESENT && fs_i != riscv::Off) begin // only generate decoder if FP extensions are enabled (static)
                        instruction_o.fu  = LOAD;
                        imm_select = IIMM;
                        instruction_o.rs1       = instr.itype.rs1;
                        instruction_o.rd        = instr.itype.rd;
                        // determine load size
                        unique case (instr.itype.funct3)
                            // Only process instruction if corresponding extension is active (static)
                            3'b000: if (XF8) instruction_o.op = ariane_pkg::FLB;
                                    else illegal_instr = 1'b1;
                            3'b001: if (XF16 | XF16ALT) instruction_o.op = ariane_pkg::FLH;
                                    else illegal_instr = 1'b1;
                            3'b010: if (RVF) instruction_o.op  = ariane_pkg::FLW;
                                    else illegal_instr = 1'b1;
                            3'b011: if (RVD) instruction_o.op  = ariane_pkg::FLD;
                                    else illegal_instr = 1'b1;
                            default: illegal_instr = 1'b1;
                        endcase
                    end else
                        illegal_instr = 1'b1;
                end

                // ----------------------------------
                // Floating-Point Reg-Reg Operations
                // ----------------------------------
                riscv::OpcodeMadd,
                riscv::OpcodeMsub,
                riscv::OpcodeNmsub,
                riscv::OpcodeNmadd: begin
                    if (FP_PRESENT && fs_i != riscv::Off) begin // only generate decoder if FP extensions are enabled (static)
                        instruction_o.fu  = FPU;
                        instruction_o.rs1 = instr.r4type.rs1;
                        instruction_o.rs2 = instr.r4type.rs2;
                        instruction_o.rd  = instr.r4type.rd;
                        imm_select        = RS3; // rs3 into result field
                        check_fprm        = 1'b1;
                        // select the correct fused operation
                        unique case (instr.r4type.opcode)
                            default:      instruction_o.op = ariane_pkg::FMADD;  // fmadd.fmt - FP Fused multiply-add
                            riscv::OpcodeMsub:  instruction_o.op = ariane_pkg::FMSUB;  // fmsub.fmt - FP Fused multiply-subtract
                            riscv::OpcodeNmsub: instruction_o.op = ariane_pkg::FNMSUB; // fnmsub.fmt - FP Negated fused multiply-subtract
                            riscv::OpcodeNmadd: instruction_o.op = ariane_pkg::FNMADD; // fnmadd.fmt - FP Negated fused multiply-add
                        endcase

                        // determine fp format
                        unique case (instr.r4type.funct2)
                            // Only process instruction if corresponding extension is active (static)
                            2'b00: if (~RVF)             illegal_instr = 1'b1;
                            2'b01: if (~RVD)             illegal_instr = 1'b1;
                            2'b10: if (~XF16 & ~XF16ALT) illegal_instr = 1'b1;
                            2'b11: if (~XF8)             illegal_instr = 1'b1;
                            default: illegal_instr = 1'b1;
                        endcase

                        // check rounding mode
                        if (check_fprm) begin
                            unique case (instr.rftype.rm) inside
                                [3'b000:3'b100]: ; //legal rounding modes
                                3'b101: begin      // Alternative Half-Precsision encded as fmt=10 and rm=101
                                    if (~XF16ALT || instr.rftype.fmt != 2'b10)
                                        illegal_instr = 1'b1;
                                    unique case (frm_i) inside // actual rounding mode from frm csr
                                        [3'b000:3'b100]: ; //legal rounding modes
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                3'b111: begin
                                    // rounding mode from frm csr
                                    unique case (frm_i) inside
                                        [3'b000:3'b100]: ; //legal rounding modes
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                default : illegal_instr = 1'b1;
                            endcase
                        end
                    end else begin
                        illegal_instr = 1'b1;
                    end
                end

                riscv::OpcodeOpFp: begin
                    if (FP_PRESENT && fs_i != riscv::Off) begin // only generate decoder if FP extensions are enabled (static)
                        instruction_o.fu  = FPU;
                        instruction_o.rs1 = instr.rftype.rs1;
                        instruction_o.rs2 = instr.rftype.rs2;
                        instruction_o.rd  = instr.rftype.rd;
                        check_fprm        = 1'b1;
                        // decode FP instruction
                        unique case (instr.rftype.funct5)
                            5'b00000: begin
                                instruction_o.op  = ariane_pkg::FADD;             // fadd.fmt - FP Addition
                                instruction_o.rs1 = '0;               // Operand A is set to 0
                                instruction_o.rs2 = instr.rftype.rs1; // Operand B is set to rs1
                                imm_select        = IIMM;             // Operand C is set to rs2
                            end
                            5'b00001: begin
                                instruction_o.op  = ariane_pkg::FSUB;  // fsub.fmt - FP Subtraction
                                instruction_o.rs1 = '0;               // Operand A is set to 0
                                instruction_o.rs2 = instr.rftype.rs1; // Operand B is set to rs1
                                imm_select        = IIMM;             // Operand C is set to rs2
                            end
                            5'b00010: instruction_o.op = ariane_pkg::FMUL;  // fmul.fmt - FP Multiplication
                            5'b00011: instruction_o.op = ariane_pkg::FDIV;  // fdiv.fmt - FP Division
                            5'b01011: begin
                                instruction_o.op = ariane_pkg::FSQRT; // fsqrt.fmt - FP Square Root
                                // rs2 must be zero
                                if (instr.rftype.rs2 != 5'b00000) illegal_instr = 1'b1;
                            end
                            5'b00100: begin
                                instruction_o.op = ariane_pkg::FSGNJ; // fsgn{j[n]/jx}.fmt - FP Sign Injection
                                check_fprm       = 1'b0;  // instruction encoded in rm, do the check here
                                if (XF16ALT) begin        // FP16ALT instructions encoded in rm separately (static)
                                    if (!(instr.rftype.rm inside {[3'b000:3'b010], [3'b100:3'b110]}))
                                        illegal_instr = 1'b1;
                                end else begin
                                    if (!(instr.rftype.rm inside {[3'b000:3'b010]}))
                                        illegal_instr = 1'b1;
                                end
                            end
                            5'b00101: begin
                                instruction_o.op = ariane_pkg::FMIN_MAX; // fmin/fmax.fmt - FP Minimum / Maximum
                                check_fprm       = 1'b0;     // instruction encoded in rm, do the check here
                                if (XF16ALT) begin           // FP16ALT instructions encoded in rm separately (static)
                                    if (!(instr.rftype.rm inside {[3'b000:3'b001], [3'b100:3'b101]}))
                                        illegal_instr = 1'b1;
                                end else begin
                                    if (!(instr.rftype.rm inside {[3'b000:3'b001]}))
                                        illegal_instr = 1'b1;
                                end
                            end
                            5'b01000: begin
                                instruction_o.op  = ariane_pkg::FCVT_F2F; // fcvt.fmt.fmt - FP to FP Conversion
                                instruction_o.rs2 = instr.rvftype.rs1; // tie rs2 to rs1 to be safe (vectors use rs2)
                                imm_select        = IIMM;     // rs2 holds part of the intruction
                                if (instr.rftype.rs2[24:23]) illegal_instr = 1'b1; // bits [22:20] used, other bits must be 0
                                // check source format
                                unique case (instr.rftype.rs2[22:20])
                                    // Only process instruction if corresponding extension is active (static)
                                    3'b000: if (~RVF)     illegal_instr = 1'b1;
                                    3'b001: if (~RVD)     illegal_instr = 1'b1;
                                    3'b010: if (~XF16)    illegal_instr = 1'b1;
                                    3'b110: if (~XF16ALT) illegal_instr = 1'b1;
                                    3'b011: if (~XF8)     illegal_instr = 1'b1;
                                    default: illegal_instr = 1'b1;
                                endcase
                            end
                            5'b10100: begin
                                instruction_o.op = ariane_pkg::FCMP; // feq/flt/fle.fmt - FP Comparisons
                                check_fprm       = 1'b0; // instruction encoded in rm, do the check here
                                if (XF16ALT) begin       // FP16ALT instructions encoded in rm separately (static)
                                    if (!(instr.rftype.rm inside {[3'b000:3'b010], [3'b100:3'b110]}))
                                        illegal_instr = 1'b1;
                                end else begin
                                    if (!(instr.rftype.rm inside {[3'b000:3'b010]}))
                                        illegal_instr = 1'b1;
                                end
                            end
                            5'b11000: begin
                                instruction_o.op = ariane_pkg::FCVT_F2I; // fcvt.ifmt.fmt - FP to Int Conversion
                                imm_select       = IIMM;     // rs2 holds part of the instruction
                                if (instr.rftype.rs2[24:22]) illegal_instr = 1'b1; // bits [21:20] used, other bits must be 0
                            end
                            5'b11010: begin
                                instruction_o.op = ariane_pkg::FCVT_I2F;  // fcvt.fmt.ifmt - Int to FP Conversion
                                imm_select       = IIMM;     // rs2 holds part of the instruction
                                if (instr.rftype.rs2[24:22]) illegal_instr = 1'b1; // bits [21:20] used, other bits must be 0
                            end
                            5'b11100: begin
                                instruction_o.rs2 = instr.rftype.rs1; // set rs2 = rs1 so we can map FMV to SGNJ in the unit
                                check_fprm        = 1'b0; // instruction encoded in rm, do the check here
                                if (instr.rftype.rm == 3'b000 || (XF16ALT && instr.rftype.rm == 3'b100)) // FP16ALT has separate encoding
                                    instruction_o.op = ariane_pkg::FMV_F2X;       // fmv.ifmt.fmt - FPR to GPR Move
                                else if (instr.rftype.rm == 3'b001 || (XF16ALT && instr.rftype.rm == 3'b101)) // FP16ALT has separate encoding
                                    instruction_o.op = ariane_pkg::FCLASS; // fclass.fmt - FP Classify
                                else illegal_instr = 1'b1;
                                // rs2 must be zero
                                if (instr.rftype.rs2 != 5'b00000) illegal_instr = 1'b1;
                            end
                            5'b11110: begin
                                instruction_o.op = ariane_pkg::FMV_X2F;   // fmv.fmt.ifmt - GPR to FPR Move
                                instruction_o.rs2 = instr.rftype.rs1; // set rs2 = rs1 so we can map FMV to SGNJ in the unit
                                check_fprm       = 1'b0; // instruction encoded in rm, do the check here
                                if (!(instr.rftype.rm == 3'b000 || (XF16ALT && instr.rftype.rm == 3'b100)))
                                    illegal_instr = 1'b1;
                                // rs2 must be zero
                                if (instr.rftype.rs2 != 5'b00000) illegal_instr = 1'b1;
                            end
                            default : illegal_instr = 1'b1;
                        endcase

                        // check format
                        unique case (instr.rftype.fmt)
                            // Only process instruction if corresponding extension is active (static)
                            2'b00: if (~RVF)             illegal_instr = 1'b1;
                            2'b01: if (~RVD)             illegal_instr = 1'b1;
                            2'b10: if (~XF16 & ~XF16ALT) illegal_instr = 1'b1;
                            2'b11: if (~XF8)             illegal_instr = 1'b1;
                            default: illegal_instr = 1'b1;
                        endcase

                        // check rounding mode
                        if (check_fprm) begin
                            unique case (instr.rftype.rm) inside
                                [3'b000:3'b100]: ; //legal rounding modes
                                3'b101: begin      // Alternative Half-Precsision encded as fmt=10 and rm=101
                                    if (~XF16ALT || instr.rftype.fmt != 2'b10)
                                        illegal_instr = 1'b1;
                                    unique case (frm_i) inside // actual rounding mode from frm csr
                                        [3'b000:3'b100]: ; //legal rounding modes
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                3'b111: begin
                                    // rounding mode from frm csr
                                    unique case (frm_i) inside
                                        [3'b000:3'b100]: ; //legal rounding modes
                                        default : illegal_instr = 1'b1;
                                    endcase
                                end
                                default : illegal_instr = 1'b1;
                            endcase
                        end
                    end else begin
                        illegal_instr = 1'b1;
                    end
                end

                // ----------------------------------
                // Atomic Operations
                // ----------------------------------
                riscv::OpcodeAmo: begin
                    // we are going to use the load unit for AMOs
                    instruction_o.fu  = STORE;
                    instruction_o.rs1[4:0] = instr.atype.rs1;
                    instruction_o.rs2[4:0] = instr.atype.rs2;
                    instruction_o.rd[4:0]  = instr.atype.rd;
                    // TODO(zarubaf): Ordering
                    // words
                    if (RVA && instr.stype.funct3 == 3'h2) begin
                        unique case (instr.instr[31:27])
                            5'h0:  instruction_o.op = ariane_pkg::AMO_ADDW;
                            5'h1:  instruction_o.op = ariane_pkg::AMO_SWAPW;
                            5'h2: begin
                                instruction_o.op = ariane_pkg::AMO_LRW;
                                if (instr.atype.rs2 != 0) illegal_instr = 1'b1;
                            end
                            5'h3:  instruction_o.op = ariane_pkg::AMO_SCW;
                            5'h4:  instruction_o.op = ariane_pkg::AMO_XORW;
                            5'h8:  instruction_o.op = ariane_pkg::AMO_ORW;
                            5'hC:  instruction_o.op = ariane_pkg::AMO_ANDW;
                            5'h10: instruction_o.op = ariane_pkg::AMO_MINW;
                            5'h14: instruction_o.op = ariane_pkg::AMO_MAXW;
                            5'h18: instruction_o.op = ariane_pkg::AMO_MINWU;
                            5'h1C: instruction_o.op = ariane_pkg::AMO_MAXWU;
                            default: illegal_instr = 1'b1;
                        endcase
                    // double words
                    end else if (RVA && instr.stype.funct3 == 3'h3) begin
                        unique case (instr.instr[31:27])
                            5'h0:  instruction_o.op = ariane_pkg::AMO_ADDD;
                            5'h1:  instruction_o.op = ariane_pkg::AMO_SWAPD;
                            5'h2: begin
                                instruction_o.op = ariane_pkg::AMO_LRD;
                                if (instr.atype.rs2 != 0) illegal_instr = 1'b1;
                            end
                            5'h3:  instruction_o.op = ariane_pkg::AMO_SCD;
                            5'h4:  instruction_o.op = ariane_pkg::AMO_XORD;
                            5'h8:  instruction_o.op = ariane_pkg::AMO_ORD;
                            5'hC:  instruction_o.op = ariane_pkg::AMO_ANDD;
                            5'h10: instruction_o.op = ariane_pkg::AMO_MIND;
                            5'h14: instruction_o.op = ariane_pkg::AMO_MAXD;
                            5'h18: instruction_o.op = ariane_pkg::AMO_MINDU;
                            5'h1C: instruction_o.op = ariane_pkg::AMO_MAXDU;
                            default: illegal_instr = 1'b1;
                        endcase
                    end else begin
                        illegal_instr = 1'b1;
                    end
                end

                // --------------------------------
                // Control Flow Instructions
                // --------------------------------
                riscv::OpcodeBranch: begin
                    imm_select              = SBIMM;
                    instruction_o.fu        = CTRL_FLOW;
                    instruction_o.rs1[4:0]  = instr.stype.rs1;
                    instruction_o.rs2[4:0]  = instr.stype.rs2;

                    is_control_flow_instr_o = 1'b1;

                    case (instr.stype.funct3)
                        3'b000: instruction_o.op = ariane_pkg::EQ;
                        3'b001: instruction_o.op = ariane_pkg::NE;
                        3'b100: instruction_o.op = ariane_pkg::LTS;
                        3'b101: instruction_o.op = ariane_pkg::GES;
                        3'b110: instruction_o.op = ariane_pkg::LTU;
                        3'b111: instruction_o.op = ariane_pkg::GEU;
                        default: begin
                            is_control_flow_instr_o = 1'b0;
                            illegal_instr           = 1'b1;
                        end
                    endcase
                end
                // Jump and link register
                riscv::OpcodeJalr: begin
                    instruction_o.fu        = CTRL_FLOW;
                    instruction_o.op        = ariane_pkg::JALR;
                    instruction_o.rs1[4:0]  = instr.itype.rs1;
                    imm_select              = IIMM;
                    instruction_o.rd[4:0]   = instr.itype.rd;
                    is_control_flow_instr_o = 1'b1;
                    // invalid jump and link register -> reserved for vector encoding
                    if (instr.itype.funct3 != 3'b0) illegal_instr = 1'b1;
                end
                // Jump and link
                riscv::OpcodeJal: begin
                    instruction_o.fu        = CTRL_FLOW;
                    imm_select              = JIMM;
                    instruction_o.rd[4:0]   = instr.utype.rd;
                    is_control_flow_instr_o = 1'b1;
                end

                riscv::OpcodeAuipc: begin
                    instruction_o.fu      = ALU;
                    imm_select            = UIMM;
                    instruction_o.use_pc  = 1'b1;
                    instruction_o.rd[4:0] = instr.utype.rd;
                end

                riscv::OpcodeLui: begin
                    imm_select            = UIMM;
                    instruction_o.fu      = ALU;
                    instruction_o.rd[4:0] = instr.utype.rd;
                end

                default: illegal_instr = 1'b1;
            endcase
        end
    end

    // --------------------------------
    // Sign extend immediate
    // --------------------------------
    always_comb begin : sign_extend
        imm_i_type  = { {riscv::XLEN-12{instruction_i[31]}}, instruction_i[31:20] };
        imm_s_type  = { {riscv::XLEN-12{instruction_i[31]}}, instruction_i[31:25], instruction_i[11:7] };
        imm_sb_type = { {riscv::XLEN-13{instruction_i[31]}}, instruction_i[31], instruction_i[7], instruction_i[30:25], instruction_i[11:8], 1'b0 };
        imm_u_type  = { {riscv::XLEN-32{instruction_i[31]}}, instruction_i[31:12], 12'b0 }; // JAL, AUIPC, sign extended to 64 bit
        imm_uj_type = { {riscv::XLEN-20{instruction_i[31]}}, instruction_i[19:12], instruction_i[20], instruction_i[30:21], 1'b0 };
        imm_bi_type = { {riscv::XLEN-5{instruction_i[24]}}, instruction_i[24:20] };

        // NOIMM, IIMM, SIMM, BIMM, UIMM, JIMM, RS3
        // select immediate
        case (imm_select)
            IIMM: begin
                instruction_o.result = imm_i_type;
                instruction_o.use_imm = 1'b1;
            end
            SIMM: begin
                instruction_o.result = imm_s_type;
                instruction_o.use_imm = 1'b1;
            end
            SBIMM: begin
                instruction_o.result = imm_sb_type;
                instruction_o.use_imm = 1'b1;
            end
            UIMM: begin
                instruction_o.result = imm_u_type;
                instruction_o.use_imm = 1'b1;
            end
            JIMM: begin
                instruction_o.result = imm_uj_type;
                instruction_o.use_imm = 1'b1;
            end
            RS3: begin
                // result holds address of fp operand rs3
                instruction_o.result = {{riscv::XLEN-5{1'b0}}, instr.r4type.rs3};
                instruction_o.use_imm = 1'b0;
            end
            default: begin
                instruction_o.result = {riscv::XLEN{1'b0}};
                instruction_o.use_imm = 1'b0;
            end
        endcase
    end

    // ---------------------
    // Exception handling
    // ---------------------
    riscv::xlen_t interrupt_cause;

    // this instruction has already executed if the exception is valid
    assign instruction_o.valid   = instruction_o.ex.valid;

    always_comb begin : exception_handling
        interrupt_cause       = '0;
        instruction_o.ex      = ex_i;
        // look if we didn't already get an exception in any previous
        // stage - we should not overwrite it as we retain order regarding the exception
        if (~ex_i.valid) begin
            // if we didn't already get an exception save the instruction here as we may need it
            // in the commit stage if we got a access exception to one of the CSR registers
            instruction_o.ex.tval  = (is_compressed_i) ? {{riscv::XLEN-16{1'b0}}, compressed_instr_i} : {{riscv::XLEN-32{1'b0}}, instruction_i};
            // instructions which will throw an exception are marked as valid
            // e.g.: they can be committed anytime and do not need to wait for any functional unit
            // check here if we decoded an invalid instruction or if the compressed decoder already decoded
            // a invalid instruction
            if (illegal_instr || is_illegal_i) begin
                instruction_o.ex.valid = 1'b1;
                // we decoded an illegal exception here
                instruction_o.ex.cause = riscv::ILLEGAL_INSTR;
            // we got an ecall, set the correct cause depending on the current privilege level
            end else if (ecall) begin
                // this exception is valid
                instruction_o.ex.valid = 1'b1;
                // depending on the privilege mode, set the appropriate cause
                case (priv_lvl_i)
                    riscv::PRIV_LVL_M: instruction_o.ex.cause = riscv::ENV_CALL_MMODE;
                    riscv::PRIV_LVL_S: instruction_o.ex.cause = riscv::ENV_CALL_SMODE;
                    riscv::PRIV_LVL_U: instruction_o.ex.cause = riscv::ENV_CALL_UMODE;
                    default:; // this should not happen
                endcase
            end else if (ebreak) begin
                // this exception is valid
                instruction_o.ex.valid = 1'b1;
                // set breakpoint cause
                instruction_o.ex.cause = riscv::BREAKPOINT;
            end
            // -----------------
            // Interrupt Control
            // -----------------
            // we decode an interrupt the same as an exception, hence it will be taken if the instruction did not
            // throw any previous exception.
            // we have three interrupt sources: external interrupts, software interrupts, timer interrupts (order of precedence)
            // for two privilege levels: Supervisor and Machine Mode
            // Supervisor Timer Interrupt
            if (irq_ctrl_i.mie[riscv::S_TIMER_INTERRUPT[$clog2(riscv::XLEN)-1:0]] && irq_ctrl_i.mip[riscv::S_TIMER_INTERRUPT[$clog2(riscv::XLEN)-1:0]]) begin
                interrupt_cause = riscv::S_TIMER_INTERRUPT;
            end
            // Supervisor Software Interrupt
            if (irq_ctrl_i.mie[riscv::S_SW_INTERRUPT[$clog2(riscv::XLEN)-1:0]] && irq_ctrl_i.mip[riscv::S_SW_INTERRUPT[$clog2(riscv::XLEN)-1:0]]) begin
                interrupt_cause = riscv::S_SW_INTERRUPT;
            end
            // Supervisor External Interrupt
            // The logical-OR of the software-writable bit and the signal from the external interrupt controller is
            // used to generate external interrupts to the supervisor
            if (irq_ctrl_i.mie[riscv::S_EXT_INTERRUPT[$clog2(riscv::XLEN)-1:0]] && (irq_ctrl_i.mip[riscv::S_EXT_INTERRUPT[$clog2(riscv::XLEN)-1:0]] | irq_i[ariane_pkg::SupervisorIrq])) begin
                interrupt_cause = riscv::S_EXT_INTERRUPT;
            end
            // Machine Timer Interrupt
            if (irq_ctrl_i.mip[riscv::M_TIMER_INTERRUPT[$clog2(riscv::XLEN)-1:0]] && irq_ctrl_i.mie[riscv::M_TIMER_INTERRUPT[$clog2(riscv::XLEN)-1:0]]) begin
                interrupt_cause = riscv::M_TIMER_INTERRUPT;
            end
            // Machine Mode Software Interrupt
            if (irq_ctrl_i.mip[riscv::M_SW_INTERRUPT[$clog2(riscv::XLEN)-1:0]] && irq_ctrl_i.mie[riscv::M_SW_INTERRUPT[$clog2(riscv::XLEN)-1:0]]) begin
                interrupt_cause = riscv::M_SW_INTERRUPT;
            end
            // Machine Mode External Interrupt
            if (irq_ctrl_i.mip[riscv::M_EXT_INTERRUPT[$clog2(riscv::XLEN)-1:0]] && irq_ctrl_i.mie[riscv::M_EXT_INTERRUPT[$clog2(riscv::XLEN)-1:0]]) begin
                interrupt_cause = riscv::M_EXT_INTERRUPT;
            end

            if (interrupt_cause[riscv::XLEN-1] && irq_ctrl_i.global_enable) begin
                // However, if bit i in mideleg is set, interrupts are considered to be globally enabled if the hart’s current privilege
                // mode equals the delegated privilege mode (S or U) and that mode’s interrupt enable bit
                // (SIE or UIE in mstatus) is set, or if the current privilege mode is less than the delegated privilege mode.
                if (irq_ctrl_i.mideleg[interrupt_cause[$clog2(riscv::XLEN)-1:0]]) begin
                    if ((irq_ctrl_i.sie && priv_lvl_i == riscv::PRIV_LVL_S) || priv_lvl_i == riscv::PRIV_LVL_U) begin
                        instruction_o.ex.valid = 1'b1;
                        instruction_o.ex.cause = interrupt_cause;
                    end
                end else begin
                    instruction_o.ex.valid = 1'b1;
                    instruction_o.ex.cause = interrupt_cause;
                end
            end
        end

        // a debug request has precendece over everything else
        if (debug_req_i && !debug_mode_i) begin
          instruction_o.ex.valid = 1'b1;
          instruction_o.ex.cause = riscv::DEBUG_REQUEST;
        end
    end
endmodule
