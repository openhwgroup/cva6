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
    input  logic            clk_i,                   // Clock
    input  logic            rst_ni,                  // Asynchronous reset active low
    input  logic [63:0]     pc_i,                    // PC from IF
    input  logic            is_compressed_i,         // is a compressed instruction
    input  logic [31:0]     instruction_i,           // instruction from IF
    input  exception        ex_i,                    // if an exception occured in if
    output scoreboard_entry instruction_o,           // scoreboard entry to scoreboard
    output logic            is_control_flow_instr_o  // this instruction will change the control flow
);
    logic illegal_instr;
    instruction instr;
    assign instr = instruction'(instruction_i);
    // --------------------
    // Immediate select
    // --------------------
    enum logic[3:0] {
        NOIMM, PCIMM, IIMM, SIMM, BIMM, UIMM, JIMM
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

        if (~ex_i.valid) begin
            case (instr.rtype.opcode)
                OPCODE_SYSTEM: begin
                    instruction_o.fu  = CSR;
                    instruction_o.rs1 = instr.itype.rs1;
                    instruction_o.rd  = instr.itype.rd;

                    unique case (instr.itype.funct3)
                        3'b000: begin
                            // TODO:
                            // ECALL, EBREAK, SFEBCE.VM
                            // MRET/SRET/URET, WFI
                            illegal_instr = 1'b1;
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
                                instruction_o.op = CSR_SET;
                        end
                        // use zimm and iimm
                        3'b101: begin// CSRRWI
                            instruction_o.rs1 = 5'b0;
                            imm_select = IIMM;
                            instruction_o.use_zimm = 1'b1;
                            instruction_o.op = CSR_WRITE;
                        end
                        3'b110: begin// CSRRSI
                            instruction_o.rs1 = 5'b0;
                            imm_select = IIMM;
                            instruction_o.use_zimm = 1'b1;
                            // this is just a read
                            if (instr.itype.rs1 == 5'b0)
                                instruction_o.op = CSR_READ;
                            else
                                instruction_o.op = CSR_SET;
                        end
                        3'b111: begin// CSRRCI
                            instruction_o.rs1 = 5'b0;
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
                    // TODO: Implement
                    // FENCE, FENCE.I,
                end

                // --------------------------
                // Reg-Reg Operations
                // --------------------------
                OPCODE_OP: begin
                    instruction_o.fu  = ALU;
                    instruction_o.rs1 = instr.rtype.rs1;
                    instruction_o.rs2 = instr.rtype.rs2;
                    instruction_o.rd  = instr.rtype.rd;

                    unique case ({instr.rtype.funct7, instr.rtype.funct3})
                        {6'b00_0000, 3'b000}: instruction_o.op = ADD;   // Add
                        {6'b10_0000, 3'b000}: instruction_o.op = SUB;   // Sub
                        {6'b00_0000, 3'b010}: instruction_o.op = SLTS;  // Set Lower Than
                        {6'b00_0000, 3'b011}: instruction_o.op = SLTU;  // Set Lower Than Unsigned
                        {6'b00_0000, 3'b100}: instruction_o.op = XORL;  // Xor
                        {6'b00_0000, 3'b110}: instruction_o.op = ORL;   // Or
                        {6'b00_0000, 3'b111}: instruction_o.op = ANDL;  // And
                        {6'b00_0000, 3'b001}: instruction_o.op = SLL;   // Shift Left Logical
                        {6'b00_0000, 3'b101}: instruction_o.op = SRL;   // Shift Right Logical
                        {6'b10_0000, 3'b101}: instruction_o.op = SRA;   // Shift Right Arithmetic
                        default: begin
                            illegal_instr = 1'b1;
                        end
                    endcase
                end

                // --------------------------
                // 32bit Reg-Reg Operations
                // --------------------------
                OPCODE_OP32: begin
                    instruction_o.fu  = ALU;
                    instruction_o.rs1 = instr.rtype.rs1;
                    instruction_o.rs2 = instr.rtype.rs2;
                    instruction_o.rd  = instr.rtype.rd;

                    if (~instr.instr[28])
                      unique case ({instr.rtype.funct7, instr.rtype.funct3})

                        {6'b00_0000, 3'b000}: instruction_o.op = ADDW; // addw
                        {6'b10_0000, 3'b000}: instruction_o.op = SUBW; // subw
                        {6'b00_0000, 3'b001}: instruction_o.op = SLLW; // sllw
                        {6'b00_0000, 3'b101}: instruction_o.op = SRLW; // srlw
                        {6'b10_0000, 3'b101}: instruction_o.op = SRAW; // sraw
                        // multiplications

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

                      default: illegal_instr = 1'b1;
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

                OPCODE_STORE: begin
                    instruction_o.fu  = LSU;
                    imm_select = SIMM;
                    instruction_o.rs1  = instr.stype.rs1;
                    instruction_o.rs2  = instr.stype.rs2;
                    // determine store size
                    unique case (instr.stype.funct3)
                        3'b000:
                            instruction_o.op  = SB;
                        3'b001:
                            instruction_o.op  = SH;
                        3'b010:
                            instruction_o.op  = SW;
                        3'b011:
                            instruction_o.op  = SD;
                        default:
                            illegal_instr = 1'b1;
                    endcase
                end

                OPCODE_LOAD: begin
                    instruction_o.fu  = LSU;
                    imm_select = IIMM;
                    instruction_o.rs1 = instr.itype.rs1;
                    instruction_o.rd  = instr.itype.rd;
                    // determine load size and signed type
                    unique case (instr.itype.funct3)
                        3'b000:
                            instruction_o.op  = LB;
                        3'b001:
                            instruction_o.op  = LH;
                        3'b010:
                            instruction_o.op  = LW;
                        3'b100:
                            instruction_o.op  = LBU;
                        3'b101:
                            instruction_o.op  = LHU;
                        3'b110:
                            instruction_o.op  = LW;
                        3'b011:
                            instruction_o.op  = LD;
                        default:
                            illegal_instr = 1'b1;
                    endcase

                end

                OPCODE_BRANCH: begin
                    // TODO: Implement
                    imm_select              = BIMM;
                    instruction_o.fu        = CTRL_FLOW;
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
                    imm_select              = UIMM;
                    instruction_o.use_pc    = 1'b1;
                    instruction_o.rd        = instr.itype.rd;
                    is_control_flow_instr_o = 1'b1;
                end
                // Jump and link
                OPCODE_JAL: begin
                    instruction_o.fu        = CTRL_FLOW;
                    instruction_o.op        = JAL;
                    imm_select              = JIMM;
                    instruction_o.use_pc    = 1'b1;
                    instruction_o.rd        = instr.utype.rd;
                    is_control_flow_instr_o = 1'b1;
                end

                OPCODE_AUIPC: begin
                    instruction_o.fu     = ALU;
                    imm_select           = UIMM;
                    instruction_o.use_pc = 1'b1;
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

    // --------------------------------
    // Exception handling
    // --------------------------------
    always_comb begin : exception_handling
        instruction_o.ex     = ex_i;
        instruction_o.valid  = 1'b0;
        // look if we didn't already get an exception in any previous
        // stage - we should not overwrite it as we retain order regarding the exception
        if (~ex_i.valid && illegal_instr) begin
            // instructions which will throw an exception are marked as valid
            // e.g.: they can be committed anytime and do not need to wait for any functional unit
            instruction_o.valid    = 1'b1;
            instruction_o.ex.valid = 1'b1;
            // we decoded an illegal exception here
            instruction_o.ex.cause = ILLEGAL_INSTR;
            // if we decoded an illegal instruction save the faulting instruction to tval
            instruction_o.ex.tval  = instruction_i;
        end
    end
endmodule