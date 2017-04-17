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
    input  logic            clk_i,          // Clock
    input  logic            rst_ni,         // Asynchronous reset active low
    input  logic [63:0]     pc_i,           // PC from IF
    input  logic [31:0]     instruction_i,  // instruction from IF
    input  exception        ex_i,           // if an exception occured in if
    output scoreboard_entry instruction_o,  // scoreboard entry to scoreboard
    output logic            illegal_instr_o
);
    instruction instr;
    assign instr = instruction'(instruction_i);
    imm_sel_t imm_select;

    logic [63:0] imm_i_type;
    logic [63:0] imm_iz_type;
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

        imm_select = NOIMM;
        illegal_instr_o = 1'b0;
        instruction_o.valid = 1'b0;
        instruction_o.ex = ex_i;
        instruction_o.fu = NONE;
        instruction_o.op = ADD;
        instruction_o.rs1 = 5'b0;
        instruction_o.rs2 = 5'b0;
        instruction_o.rd = 5'b0;

        if (~ex_i.valid) begin
            case (instr.rtype.opcode)
                OPCODE_SYSTEM: begin
                    // TODO: Implement
                end

                OPCODE_FENCE: begin
                    // TODO: Implement
                end

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
                            illegal_instr_o = 1'b1;
                        end
                    endcase
                end

                OPCODE_OP32: begin
                    instruction_o.fu  = ALU;
                    instruction_o.rs1 = instr.rtype.rs1;
                    instruction_o.rs2 = instr.rtype.rs2;
                    instruction_o.rd  = instr.rtype.rd;
                end

                OPCODE_OPIMM: begin
                    instruction_o.fu  = ALU;
                    imm_select = IIMM;
                    instruction_o.rs1 = instr.itype.rs1;
                    instruction_o.rd  = instr.itype.rd;
                end

                OPCODE_OPIMM32: begin
                    instruction_o.fu  = ALU;
                    imm_select = IIMM;
                    instruction_o.rs1 = instr.itype.rs1;
                    instruction_o.rd  = instr.itype.rd;
                end

                OPCODE_STORE: begin
                    imm_select = SIMM;
                end

                OPCODE_LOAD: begin
                    imm_select = IIMM;
                end

                OPCODE_BRANCH: begin
                    imm_select = BIMM;
                end

                OPCODE_JALR: begin
                    imm_select = UIMM;
                end

                OPCODE_JAL: begin
                    imm_select = JIMM;
                end

                OPCODE_AUIPC: begin
                    imm_select = UIMM;
                end

                OPCODE_LUI: begin
                    imm_select = UIMM;
                end

                default: illegal_instr_o = 1'b1;
            endcase
        end
    end

    always_comb begin : sign_extend
        imm_i_type  = { {52 {instruction_i[31]}}, instruction_i[31:20] };
        imm_iz_type = {  52'b0, instruction_i[31:20] };
        imm_s_type  = { {52 {instruction_i[31]}}, instruction_i[31:25], instruction_i[11:7] };
        imm_sb_type = { {51 {instruction_i[31]}}, instruction_i[31], instruction_i[7], instruction_i[30:25], instruction_i[11:8], 1'b0 };
        imm_u_type  = { {32 {instruction_i[31]}}, instruction_i[31:12], 12'b0 }; // JAL, AUIPC, sign extended to 64 bit
        imm_uj_type = { {44 {instruction_i[31]}}, instruction_i[19:12], instruction_i[20], instruction_i[30:21], 1'b0 };
        // imm_z_type  = {  59'b0, instruction_i[`REG_S1] };
        imm_s2_type = { 59'b0, instruction_i[24:20] };
        imm_bi_type = { {59{instruction_i[24]}}, instruction_i[24:20] };
        imm_s3_type = { 59'b0, instruction_i[29:25] };
        imm_vs_type = { {58 {instruction_i[24]}}, instruction_i[24:20], instruction_i[25] };
        imm_vu_type = { 58'b0, instruction_i[24:20], instruction_i[25] };

        //  NOIMM, PCIMM, IIMM, SIMM, BIMM, BIMM, UIMM, JIMM
        // select immediate
        case (imm_select)
            PCIMM: begin
                instruction_o.imm = pc_i;
                instruction_o.use_imm = 1'b1;
            end
            IIMM: begin
                instruction_o.imm = imm_i_type;
                instruction_o.use_imm = 1'b1;
            end
            SIMM: begin
                instruction_o.imm = imm_s_type;
                instruction_o.use_imm = 1'b1;
            end
            BIMM: begin
                instruction_o.imm = imm_bi_type;
                instruction_o.use_imm = 1'b1;
            end
            UIMM: begin
                instruction_o.imm = imm_u_type;
                instruction_o.use_imm = 1'b1;
            end
            JIMM: begin
                instruction_o.imm = imm_uj_type;
                instruction_o.use_imm = 1'b1;
            end
            default: begin
                instruction_o.imm = 64'b0;
                instruction_o.use_imm = 1'b0;
            end
        endcase
    end

endmodule