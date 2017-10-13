/* File:   issue_read_operands.sv
 * Author: Florian Zaruba <zarubaf@ethz.ch>
 * Date:   8.4.2017
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * Description: Issues instruction from the scoreboard and fetches the operands
 *              This also includes all the forwarding logic
 */
import ariane_pkg::*;

module decoder (
    input  logic [63:0]        pc_i,                    // PC from IF
    input  logic               is_compressed_i,         // is a compressed instruction
    input  logic               is_illegal_i,            // illegal compressed instruction
    input  logic [31:0]        instruction_i,           // instruction from IF
    input  branchpredict_sbe_t branch_predict_i,
    input  exception_t         ex_i,                    // if an exception occured in if
    // From CSR
    input  priv_lvl_t          priv_lvl_i,              // current privilege level
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
    instruction_t instr;
    assign instr = instruction_t'(instruction_i);
    // --------------------
    // Immediate select
    // --------------------
    enum logic[3:0] {
        NOIMM, PCIMM, IIMM, SIMM, SBIMM, BIMM, UIMM, JIMM
    } imm_select;

    logic [63:0] imm_i_type;
    logic [11:0] imm_iz_type;
    logic [63:0] imm_s_type;
    logic [63:0] imm_sb_type;
    logic [63:0] imm_u_type;
    logic [63:0] imm_uj_type;
    logic [63:0] imm_z_type;
    logic [63:0] imm_s2_type;
    logic [63:0] imm_bi_type;
    logic [63:0] imm_s3_type;
    logic [63:0] imm_vs_type;
    logic [63:0] imm_vu_type;

    always_comb begin : decoder

        imm_select                  = NOIMM;
        is_control_flow_instr_o     = 1'b0;
        illegal_instr               = 1'b0;
        instruction_o.pc            = pc_i;
        instruction_o.fu            = NONE;
        instruction_o.op            = ADD;
        instruction_o.rs1           = 5'b0;
        instruction_o.rs2           = 5'b0;
        instruction_o.rd            = 5'b0;
        instruction_o.use_pc        = 1'b0;
        instruction_o.trans_id      = 5'b0;
        instruction_o.is_compressed = is_compressed_i;
        instruction_o.use_zimm      = 1'b0;
        instruction_o.bp            = branch_predict_i;
        ecall                       = 1'b0;
        ebreak                      = 1'b0;

        if (~ex_i.valid) begin
            case (instr.rtype.opcode)
                OPCODE_SYSTEM: begin
                    instruction_o.fu  = CSR;
                    instruction_o.rs1 = instr.itype.rs1;
                    instruction_o.rd  = instr.itype.rd;

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
                                12'b100000010: begin
                                    instruction_o.op = SRET;
                                    // check privilege level, SRET can only be executed in S and M mode
                                    // we'll just decode an illegal instruction if we are in the wrong privilege level
                                    if (priv_lvl_i == PRIV_LVL_U) begin
                                        illegal_instr = 1'b1;
                                        //  do not change privilege level if this is an illegal instruction
                                        instruction_o.op = ADD;
                                    end
                                    // if we are in S-Mode and Trap SRET (tsr) is set -> trap on illegal instruction
                                    if (priv_lvl_i == PRIV_LVL_S && tsr_i) begin
                                        illegal_instr = 1'b1;
                                        //  do not change privilege level if this is an illegal instruction
                                       instruction_o.op = ADD;
                                    end
                                end
                                // MRET
                                12'b1100000010: begin
                                    instruction_o.op = MRET;
                                    // check privilege level, MRET can only be executed in M mode
                                    // otherwise we decode an illegal instruction
                                    if (priv_lvl_i inside {PRIV_LVL_U, PRIV_LVL_S})
                                        illegal_instr = 1'b1;
                                end
                                // WFI
                                12'b1_0000_0101: begin
                                    instruction_o.op = WFI;
                                    // if timeout wait is set, trap on an illegal instruction in S Mode
                                    // (after 0 cycles timeout)
                                    if (priv_lvl_i == PRIV_LVL_S && tw_i) begin
                                        illegal_instr = 1'b1;
                                        instruction_o.op = ADD;
                                    end
                                    // we don't support U mode interrupts so WFI is illegal in this context
                                    if (priv_lvl_i == PRIV_LVL_U) begin
                                        illegal_instr = 1'b1;
                                        instruction_o.op = ADD;
                                    end
                                end
                                // SFENCE.VMA
                                default: begin
                                    if (instr.instr[31:25] == 7'b1001) begin
                                        // Reset illegal instruction here, this is the only type
                                        // of instruction which needs those kind of fields
                                        illegal_instr    = 1'b0;
                                        instruction_o.op = SFENCE_VMA;
                                        // check TVM flag and intercept SFENCE.VMA call if necessary
                                        if (priv_lvl_i == PRIV_LVL_S && tvm_i)
                                            illegal_instr = 1'b1;
                                    end
                                end
                            endcase
                        end
                        // atomically swaps values in the CSR and integer register
                        3'b001: begin// CSRRW
                            imm_select = IIMM;
                            instruction_o.op = CSR_WRITE;
                        end
                        // atomically set values in the CSR and write back to rd
                        3'b010: begin// CSRRS
                            imm_select = IIMM;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = CSR_READ;
                            else
                                instruction_o.op = CSR_SET;
                        end
                        // atomically clear values in the CSR and write back to rd
                        3'b011: begin// CSRRC
                            imm_select = IIMM;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = CSR_READ;
                            else
                                instruction_o.op = CSR_CLEAR;
                        end
                        // use zimm and iimm
                        3'b101: begin// CSRRWI
                            instruction_o.rs1 = instr.itype.rs1;
                            imm_select = IIMM;
                            instruction_o.use_zimm = 1'b1;
                            instruction_o.op = CSR_WRITE;
                        end
                        3'b110: begin// CSRRSI
                            instruction_o.rs1 = instr.itype.rs1;
                            imm_select = IIMM;
                            instruction_o.use_zimm = 1'b1;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = CSR_READ;
                            else
                                instruction_o.op = CSR_SET;
                        end
                        3'b111: begin// CSRRCI
                            instruction_o.rs1 = instr.itype.rs1;
                            imm_select = IIMM;
                            instruction_o.use_zimm = 1'b1;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = CSR_READ;
                            else
                                instruction_o.op = CSR_CLEAR;
                        end
                        default: illegal_instr = 1'b1;
                    endcase
                end

                OPCODE_FENCE: begin
                    // FENCE.I
                    if (instr.itype.funct3 == 3'b001) begin
                        instruction_o.fu  = CSR;
                        instruction_o.op  = FENCE_I;
                        instruction_o.rs1 = '0;
                        instruction_o.rs2 = '0;
                        instruction_o.rd  = '0;
                    // FENCE
                    end else begin
                        // Currently implemented as a whole DCache flush boldly ignoring other things
                        instruction_o.fu  = CSR;
                        instruction_o.op  = FENCE;
                        instruction_o.rs1 = '0;
                        instruction_o.rs2 = '0;
                        instruction_o.rd  = '0;
                    end
                end

                // --------------------------
                // Reg-Reg Operations
                // --------------------------
                OPCODE_OP: begin
                    instruction_o.fu  = (instr.rtype.funct7 == 7'b000_0001) ? MULT : ALU;
                    instruction_o.rs1 = instr.rtype.rs1;
                    instruction_o.rs2 = instr.rtype.rs2;
                    instruction_o.rd  = instr.rtype.rd;

                    unique case ({instr.rtype.funct7, instr.rtype.funct3})
                        {7'b000_0000, 3'b000}: instruction_o.op = ADD;   // Add
                        {7'b010_0000, 3'b000}: instruction_o.op = SUB;   // Sub
                        {7'b000_0000, 3'b010}: instruction_o.op = SLTS;  // Set Lower Than
                        {7'b000_0000, 3'b011}: instruction_o.op = SLTU;  // Set Lower Than Unsigned
                        {7'b000_0000, 3'b100}: instruction_o.op = XORL;  // Xor
                        {7'b000_0000, 3'b110}: instruction_o.op = ORL;   // Or
                        {7'b000_0000, 3'b111}: instruction_o.op = ANDL;  // And
                        {7'b000_0000, 3'b001}: instruction_o.op = SLL;   // Shift Left Logical
                        {7'b000_0000, 3'b101}: instruction_o.op = SRL;   // Shift Right Logical
                        {7'b010_0000, 3'b101}: instruction_o.op = SRA;   // Shift Right Arithmetic
                        // Multiplications
                        `ifdef MULT
                        {7'b000_0001, 3'b000}: instruction_o.op = MUL;
                        {7'b000_0001, 3'b001}: instruction_o.op = MULH;
                        {7'b000_0001, 3'b010}: instruction_o.op = MULHSU;
                        {7'b000_0001, 3'b011}: instruction_o.op = MULHU;
                        {7'b000_0001, 3'b100}: instruction_o.op = DIV;
                        {7'b000_0001, 3'b101}: instruction_o.op = DIVU;
                        {7'b000_0001, 3'b110}: instruction_o.op = REM;
                        {7'b000_0001, 3'b111}: instruction_o.op = REMU;
                        `endif
                        default: begin
                            illegal_instr = 1'b1;
                        end
                    endcase
                end

                // --------------------------
                // 32bit Reg-Reg Operations
                // --------------------------
                OPCODE_OP32: begin
                    instruction_o.fu  = (instr.rtype.funct7 == 7'b000_0001) ? MULT : ALU;
                    instruction_o.rs1 = instr.rtype.rs1;
                    instruction_o.rs2 = instr.rtype.rs2;
                    instruction_o.rd  = instr.rtype.rd;

                    if (~instr.instr[28])
                      unique case ({instr.rtype.funct7, instr.rtype.funct3})

                        {7'b000_0000, 3'b000}: instruction_o.op = ADDW; // addw
                        {7'b010_0000, 3'b000}: instruction_o.op = SUBW; // subw
                        {7'b000_0000, 3'b001}: instruction_o.op = SLLW; // sllw
                        {7'b000_0000, 3'b101}: instruction_o.op = SRLW; // srlw
                        {7'b010_0000, 3'b101}: instruction_o.op = SRAW; // sraw
                        // Multiplications
                        `ifdef MULT
                        {7'b000_0001, 3'b000}: instruction_o.op = MULW;
                        {7'b000_0001, 3'b100}: instruction_o.op = DIVW;
                        {7'b000_0001, 3'b101}: instruction_o.op = DIVUW;
                        {7'b000_0001, 3'b110}: instruction_o.op = REMW;
                        {7'b000_0001, 3'b111}: instruction_o.op = REMUW;
                        `endif
                        default: illegal_instr = 1'b1;
                      endcase
                end
                // --------------------------------
                // Reg-Immediate Operations
                // --------------------------------
                OPCODE_OPIMM: begin
                    instruction_o.fu  = ALU;
                    imm_select = IIMM;
                    instruction_o.rs1 = instr.itype.rs1;
                    instruction_o.rd  = instr.itype.rd;

                    unique case (instr.itype.funct3)
                      3'b000: instruction_o.op = ADD;   // Add Immediate
                      3'b010: instruction_o.op = SLTS;  // Set to one if Lower Than Immediate
                      3'b011: instruction_o.op = SLTU;  // Set to one if Lower Than Immediate Unsigned
                      3'b100: instruction_o.op = XORL;  // Exclusive Or with Immediate
                      3'b110: instruction_o.op = ORL;   // Or with Immediate
                      3'b111: instruction_o.op = ANDL;  // And with Immediate

                      3'b001: begin
                        instruction_o.op = SLL;  // Shift Left Logical by Immediate
                        if (instr.instr[31:26] != 6'b0)
                          illegal_instr = 1'b1;
                      end

                      3'b101: begin
                        if (instr.instr[31:26] == 6'b0)
                          instruction_o.op = SRL;  // Shift Right Logical by Immediate
                        else if (instr.instr[31:26] == 6'b010_000)
                          instruction_o.op = SRA;  // Shift Right Arithmetically by Immediate
                        else
                          illegal_instr = 1'b1;
                      end
                    endcase
                end

                // --------------------------------
                // 32 bit Reg-Immediate Operations
                // --------------------------------
                OPCODE_OPIMM32: begin
                    instruction_o.fu  = ALU;
                    imm_select = IIMM;
                    instruction_o.rs1 = instr.itype.rs1;
                    instruction_o.rd  = instr.itype.rd;

                    unique case (instr.itype.funct3)
                      3'b000: instruction_o.op = ADDW;  // Add Immediate

                      3'b001: begin
                        instruction_o.op = SLLW;  // Shift Left Logical by Immediate
                        if (instr.instr[31:25] != 7'b0)
                          illegal_instr = 1'b1;
                      end

                      3'b101: begin
                        if (instr.instr[31:25] == 7'b0)
                          instruction_o.op = SRLW;  // Shift Right Logical by Immediate
                        else if (instr.instr[31:25] == 7'b010_0000)
                          instruction_o.op = SRAW;  // Shift Right Arithmetically by Immediate
                        else
                          illegal_instr = 1'b1;
                      end

                      default: illegal_instr = 1'b1;
                    endcase
                end
                // --------------------------------
                // LSU
                // --------------------------------
                OPCODE_STORE: begin
                    instruction_o.fu  = STORE;
                    imm_select = SIMM;
                    instruction_o.rs1  = instr.stype.rs1;
                    instruction_o.rs2  = instr.stype.rs2;
                    // determine store size
                    unique case (instr.stype.funct3)
                        3'b000: instruction_o.op  = SB;
                        3'b001: instruction_o.op  = SH;
                        3'b010: instruction_o.op  = SW;
                        3'b011: instruction_o.op  = SD;
                        default: illegal_instr = 1'b1;
                    endcase
                end

                OPCODE_LOAD: begin
                    instruction_o.fu  = LOAD;
                    imm_select = IIMM;
                    instruction_o.rs1 = instr.itype.rs1;
                    instruction_o.rd  = instr.itype.rd;
                    // determine load size and signed type
                    unique case (instr.itype.funct3)
                        3'b000: instruction_o.op  = LB;
                        3'b001: instruction_o.op  = LH;
                        3'b010: instruction_o.op  = LW;
                        3'b100: instruction_o.op  = LBU;
                        3'b101: instruction_o.op  = LHU;
                        3'b110: instruction_o.op  = LWU;
                        3'b011: instruction_o.op  = LD;
                        default: illegal_instr = 1'b1;
                    endcase
                end

                OPCODE_AMO: begin
                    // we are going to use the load unit for AMOs
                    instruction_o.fu  = LOAD;
                    instruction_o.rd  = instr.stype.imm0;
                    instruction_o.rs1 = instr.itype.rs1;
                    // words
                    if (instr.stype.funct3 == 3'h2) begin
                        unique case (instr.instr[31:27])
                            5'h0:  instruction_o.op = AMO_ADDW;
                            5'h1:  instruction_o.op = AMO_SWAPW;
                            5'h2:  instruction_o.op = AMO_LRW;
                            5'h3:  instruction_o.op = AMO_SCW;
                            5'h4:  instruction_o.op = AMO_XORW;
                            5'h8:  instruction_o.op = AMO_ORW;
                            5'hC:  instruction_o.op = AMO_ANDW;
                            5'h10: instruction_o.op = AMO_MINW;
                            5'h14: instruction_o.op = AMO_MAXW;
                            5'h18: instruction_o.op = AMO_MINWU;
                            5'h1C: instruction_o.op = AMO_MAXWU;
                            default: illegal_instr = 1'b1;
                        endcase
                    // double words
                    end else if (instr.stype.funct3 == 3'h3) begin
                        unique case (instr.instr[31:27])
                            5'h0:  instruction_o.op = AMO_ADDD;
                            5'h1:  instruction_o.op = AMO_SWAPD;
                            5'h2:  instruction_o.op = AMO_LRD;
                            5'h3:  instruction_o.op = AMO_SCD;
                            5'h4:  instruction_o.op = AMO_XORD;
                            5'h8:  instruction_o.op = AMO_ORD;
                            5'hC:  instruction_o.op = AMO_ANDD;
                            5'h10: instruction_o.op = AMO_MIND;
                            5'h14: instruction_o.op = AMO_MAXD;
                            5'h18: instruction_o.op = AMO_MINDU;
                            5'h1C: instruction_o.op = AMO_MAXDU;
                            default: illegal_instr = 1'b1;
                        endcase
                    end else begin
                        illegal_instr = 1'b1;
                    end
                end

                // --------------------------------
                // Control Flow Instructions
                // --------------------------------
                OPCODE_BRANCH: begin
                    imm_select              = SBIMM;
                    instruction_o.fu        = CTRL_FLOW;
                    instruction_o.rs1       = instr.stype.rs1;
                    instruction_o.rs2       = instr.stype.rs2;

                    is_control_flow_instr_o = 1'b1;

                    case (instr.stype.funct3)
                        3'b000: instruction_o.op = EQ;
                        3'b001: instruction_o.op = NE;
                        3'b100: instruction_o.op = LTS;
                        3'b101: instruction_o.op = GES;
                        3'b110: instruction_o.op = LTU;
                        3'b111: instruction_o.op = GEU;
                        default: begin
                            is_control_flow_instr_o = 1'b0;
                            illegal_instr           = 1'b1;
                        end
                    endcase
                end
                // Jump and link register
                OPCODE_JALR: begin
                    instruction_o.fu        = CTRL_FLOW;
                    instruction_o.op        = JALR;
                    instruction_o.rs1       = instr.itype.rs1;
                    imm_select              = IIMM;
                    instruction_o.rd        = instr.itype.rd;
                    is_control_flow_instr_o = 1'b1;
                end
                // Jump and link
                OPCODE_JAL: begin
                    instruction_o.fu        = CTRL_FLOW;
                    imm_select              = JIMM;
                    instruction_o.rd        = instr.utype.rd;
                    is_control_flow_instr_o = 1'b1;
                end

                OPCODE_AUIPC: begin
                    instruction_o.fu     = ALU;
                    imm_select           = UIMM;
                    instruction_o.use_pc = 1'b1;
                    instruction_o.rd     = instr.utype.rd;
                end

                OPCODE_LUI: begin
                    imm_select           = UIMM;
                    instruction_o.fu     = ALU;
                    instruction_o.rd     = instr.utype.rd;
                end

                default: illegal_instr = 1'b1;
            endcase
        end
    end
    // --------------------------------
    // Sign extend immediate
    // --------------------------------
    always_comb begin : sign_extend
        imm_i_type  = { {52 {instruction_i[31]}}, instruction_i[31:20] };
        imm_iz_type = {  52'b0, instruction_i[31:20] };
        imm_s_type  = { {52 {instruction_i[31]}}, instruction_i[31:25], instruction_i[11:7] };
        imm_sb_type = { {51 {instruction_i[31]}}, instruction_i[31], instruction_i[7], instruction_i[30:25], instruction_i[11:8], 1'b0 };
        imm_u_type  = { {32 {instruction_i[31]}}, instruction_i[31:12], 12'b0 }; // JAL, AUIPC, sign extended to 64 bit
        imm_uj_type = { {44 {instruction_i[31]}}, instruction_i[19:12], instruction_i[20], instruction_i[30:21], 1'b0 };
        imm_s2_type = { 59'b0, instruction_i[24:20] };
        imm_bi_type = { {59{instruction_i[24]}}, instruction_i[24:20] };
        imm_s3_type = { 59'b0, instruction_i[29:25] };
        imm_vs_type = { {58 {instruction_i[24]}}, instruction_i[24:20], instruction_i[25] };
        imm_vu_type = { 58'b0, instruction_i[24:20], instruction_i[25] };

        // NOIMM, PCIMM, IIMM, SIMM, BIMM, BIMM, UIMM, JIMM
        // select immediate
        case (imm_select)
            PCIMM: begin
                instruction_o.result = pc_i;
                instruction_o.use_imm = 1'b1;
            end
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
            BIMM: begin
                instruction_o.result = imm_bi_type;
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
            default: begin
                instruction_o.result = 64'b0;
                instruction_o.use_imm = 1'b0;
            end
        endcase
    end

    // ---------------------
    // Exception handling
    // ---------------------
    always_comb begin : exception_handling
        instruction_o.ex      = ex_i;
        instruction_o.valid   = ex_i.valid;
        // look if we didn't already get an exception in any previous
        // stage - we should not overwrite it as we retain order regarding the exception
        if (~ex_i.valid) begin
            // if we didn't already get an exception save the instruction here as we may need it
            // in the commit stage if we got a access exception to one of the CSR registers
            instruction_o.ex.tval  = instruction_i;
            // instructions which will throw an exception are marked as valid
            // e.g.: they can be committed anytime and do not need to wait for any functional unit
            // check here if we decoded an invalid instruction or if the compressed decoder already decoded
            // a invalid instruction
            if (illegal_instr || is_illegal_i) begin
                instruction_o.valid    = 1'b1;
                instruction_o.ex.valid = 1'b1;
                // we decoded an illegal exception here
                instruction_o.ex.cause = ILLEGAL_INSTR;
            // we got an ecall, set the correct cause depending on the current privilege level
            end else if (ecall) begin
                // this instruction has already executed
                instruction_o.valid    = 1'b1;
                // this exception is valid
                instruction_o.ex.valid = 1'b1;
                // depending on the privilege mode, set the appropriate cause
                case (priv_lvl_i)
                    PRIV_LVL_M: instruction_o.ex.cause = ENV_CALL_MMODE;
                    PRIV_LVL_S: instruction_o.ex.cause = ENV_CALL_SMODE;
                    PRIV_LVL_U: instruction_o.ex.cause = ENV_CALL_UMODE;
                    default:; // this should not happen
                endcase
            end else if (ebreak) begin
                // this instruction has already executed
                instruction_o.valid    = 1'b1;
                // this exception is valid
                instruction_o.ex.valid = 1'b1;
                // set breakpoint cause
                instruction_o.ex.cause = BREAKPOINT;
            end
        end
    end
endmodule
