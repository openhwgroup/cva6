// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.                                          //
//
// Engineer:       Sven Stucki - svstucki@student.ethz.ch
//
// Design Name:    Compressed instruction decoder
// Project Name:   zero-riscy
// Language:       SystemVerilog
//
// Description:    Decodes RISC-V compressed instructions into their RV32
//                 equivalent. This module is fully combinatorial.

import ariane_pkg::*;

module compressed_decoder
(
    input  logic [31:0] instr_i,
    output logic [31:0] instr_o,
    output logic        illegal_instr_o,
    output logic        is_compressed_o
);

    // -------------------
    // Compressed Decoder
    // -------------------
    always_comb begin
        illegal_instr_o = 1'b0;
        instr_o         = '0;
        is_compressed_o = 1'b1;
        instr_o         = instr_i;

        // I: |    imm[11:0]    | rs1 | funct3 |    rd    | opcode |
        // S: | imm[11:5] | rs2 | rs1 | funct3 | imm[4:0] | opcode |
        unique case (instr_i[1:0])
            // C0
            riscv::OpcodeC0: begin
                unique case (instr_i[15:13])
                    riscv::OpcodeC0Addi4spn: begin
                        // c.addi4spn -> addi rd', x2, imm
                        instr_o = {2'b0, instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6], 2'b00, 5'h02, 3'b000, 2'b01, instr_i[4:2], riscv::OpcodeOpImm};
                        if (instr_i[12:5] == 8'b0)  illegal_instr_o = 1'b1;
                    end

                    riscv::OpcodeC0Fld: begin
                        // c.fld -> fld rd', imm(rs1')
                        // CLD: | funct3 | imm[5:3] | rs1' | imm[7:6] | rd' | C0 |
                        instr_o = {4'b0, instr_i[6:5], instr_i[12:10], 3'b000, 2'b01, instr_i[9:7], 3'b011, 2'b01, instr_i[4:2], riscv::OpcodeLoadFp};
                    end

                    riscv::OpcodeC0Lw: begin
                        // c.lw -> lw rd', imm(rs1')
                        instr_o = {5'b0, instr_i[5], instr_i[12:10], instr_i[6], 2'b00, 2'b01, instr_i[9:7], 3'b010, 2'b01, instr_i[4:2], riscv::OpcodeLoad};
                    end

                    riscv::OpcodeC0Ld: begin
                        // c.ld -> ld rd', imm(rs1')
                        // CLD: | funct3 | imm[5:3] | rs1' | imm[7:6] | rd' | C0 |
                        instr_o = {4'b0, instr_i[6:5], instr_i[12:10], 3'b000, 2'b01, instr_i[9:7], 3'b011, 2'b01, instr_i[4:2], riscv::OpcodeLoad};
                    end

                    riscv::OpcodeC0Fsd: begin
                        // c.fsd -> fsd rs2', imm(rs1')
                        instr_o = {4'b0, instr_i[6:5], instr_i[12], 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b011, instr_i[11:10], 3'b000, riscv::OpcodeStoreFp};
                    end

                    riscv::OpcodeC0Sw: begin
                        // c.sw -> sw rs2', imm(rs1')
                        instr_o = {5'b0, instr_i[5], instr_i[12], 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b010, instr_i[11:10], instr_i[6], 2'b00, riscv::OpcodeStore};
                    end

                    riscv::OpcodeC0Sd: begin
                        // c.sd -> sd rs2', imm(rs1')
                        instr_o = {4'b0, instr_i[6:5], instr_i[12], 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b011, instr_i[11:10], 3'b000, riscv::OpcodeStore};
                    end

                    default: begin
                        illegal_instr_o = 1'b1;
                    end
              endcase
            end

            // C1
            riscv::OpcodeC1: begin
                unique case (instr_i[15:13])
                    riscv::OpcodeC1Addi: begin
                        // c.addi -> addi rd, rd, nzimm
                        // c.nop -> addi 0, 0, 0
                        instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], riscv::OpcodeOpImm};
                    end

                    // c.addiw -> addiw rd, rd, nzimm for RV64
                    riscv::OpcodeC1Addiw: begin
                        if (instr_i[11:7] != 5'h0) // only valid if the destination is not r0
                            instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], riscv::OpcodeOpImm32};
                        else
                            illegal_instr_o = 1'b1;
                    end

                    riscv::OpcodeC1Li: begin
                        // c.li -> addi rd, x0, nzimm
                        instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], riscv::OpcodeOpImm};
                        if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
                    end

                    riscv::OpcodeC1LuiAddi16sp: begin
                        // c.lui -> lui rd, imm
                        instr_o = {{15 {instr_i[12]}}, instr_i[6:2], instr_i[11:7], riscv::OpcodeLui};

                        if (instr_i[11:7] == 5'h02) begin
                            // c.addi16sp -> addi x2, x2, nzimm
                            instr_o = {{3 {instr_i[12]}}, instr_i[4:3], instr_i[5], instr_i[2], instr_i[6], 4'b0, 5'h02, 3'b000, 5'h02, riscv::OpcodeOpImm};
                        end else if (instr_i[11:7] == 5'b0) begin
                            illegal_instr_o = 1'b1;
                        end

                        if ({instr_i[12], instr_i[6:2]} == 6'b0) illegal_instr_o = 1'b1;
                    end

                    riscv::OpcodeC1MiscAlu: begin
                        unique case (instr_i[11:10])
                            2'b00,
                            2'b01: begin
                                // 00: c.srli -> srli rd, rd, shamt
                                // 01: c.srai -> srai rd, rd, shamt
                                instr_o = {1'b0, instr_i[10], 4'b0, instr_i[12], instr_i[6:2], 2'b01, instr_i[9:7], 3'b101, 2'b01, instr_i[9:7], riscv::OpcodeOpImm};
                                // shamt field must be non-zero
                                if ({instr_i[12], instr_i[6:2]} == 6'b0) illegal_instr_o = 1'b1;
                            end

                            2'b10: begin
                                // c.andi -> andi rd, rd, imm
                                instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 2'b01, instr_i[9:7], 3'b111, 2'b01, instr_i[9:7], riscv::OpcodeOpImm};
                            end

                            2'b11: begin
                                unique case ({instr_i[12], instr_i[6:5]})
                                    3'b000: begin
                                        // c.sub -> sub rd', rd', rs2'
                                        instr_o = {2'b01, 5'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b000, 2'b01, instr_i[9:7], riscv::OpcodeOp};
                                    end

                                    3'b001: begin
                                        // c.xor -> xor rd', rd', rs2'
                                        instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b100, 2'b01, instr_i[9:7], riscv::OpcodeOp};
                                    end

                                    3'b010: begin
                                        // c.or  -> or  rd', rd', rs2'
                                        instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b110, 2'b01, instr_i[9:7], riscv::OpcodeOp};
                                    end

                                    3'b011: begin
                                        // c.and -> and rd', rd', rs2'
                                        instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b111, 2'b01, instr_i[9:7], riscv::OpcodeOp};
                                    end

                                    3'b100: begin
                                        // c.subw -> subw rd', rd', rs2'
                                        instr_o = {2'b01, 5'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b000, 2'b01, instr_i[9:7], riscv::OpcodeOp32};
                                    end
                                    3'b101: begin
                                        // c.addw -> addw rd', rd', rs2'
                                        instr_o = {2'b00, 5'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b000, 2'b01, instr_i[9:7], riscv::OpcodeOp32};
                                    end

                                    3'b110,
                                    3'b111: begin
                                        // 100: c.subw
                                        // 101: c.addw
                                        illegal_instr_o = 1'b1;
                                        instr_o = {16'b0, instr_i};
                                    end
                                endcase
                            end
                        endcase
                    end

                    riscv::OpcodeC1J: begin
                        // 101: c.j   -> jal x0, imm
                        instr_o = {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], {9 {instr_i[12]}}, 4'b0, ~instr_i[15], riscv::OpcodeJal};
                    end

                    riscv::OpcodeC1Beqz, riscv::OpcodeC1Bnez: begin
                        // 0: c.beqz -> beq rs1', x0, imm
                        // 1: c.bnez -> bne rs1', x0, imm
                        instr_o = {{4 {instr_i[12]}}, instr_i[6:5], instr_i[2], 5'b0, 2'b01, instr_i[9:7], 2'b00, instr_i[13], instr_i[11:10], instr_i[4:3], instr_i[12], riscv::OpcodeBranch};
                    end
                endcase
            end

            // C2
            riscv::OpcodeC2: begin
                unique case (instr_i[15:13])
                    riscv::OpcodeC2Slli: begin
                        // c.slli -> slli rd, rd, shamt
                        instr_o = {6'b0, instr_i[12], instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], riscv::OpcodeOpImm};
                        if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1; // register not x0
                        if ({instr_i[12], instr_i[6:2]}  == 6'b0)  illegal_instr_o = 1'b1; // shift amount must be non zero
                    end

                    riscv::OpcodeC2Fldsp: begin
                        // c.fldsp -> fld rd, imm(x2)
                        instr_o = {3'b0, instr_i[4:2], instr_i[12], instr_i[6:5], 3'b000, 5'h02, 3'b011, instr_i[11:7], riscv::OpcodeLoadFp};
                        if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
                    end

                    riscv::OpcodeC2Lwsp: begin
                        // c.lwsp -> lw rd, imm(x2)
                        instr_o = {4'b0, instr_i[3:2], instr_i[12], instr_i[6:4], 2'b00, 5'h02, 3'b010, instr_i[11:7], riscv::OpcodeLoad};
                        if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
                    end

                    riscv::OpcodeC2Ldsp: begin
                        // c.ldsp -> ld rd, imm(x2)
                        instr_o = {3'b0, instr_i[4:2], instr_i[12], instr_i[6:5], 3'b000, 5'h02, 3'b011, instr_i[11:7], riscv::OpcodeLoad};
                        if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
                    end

                    riscv::OpcodeC2JalrMvAdd: begin
                        if (instr_i[12] == 1'b0) begin
                            // c.mv -> add rd/rs1, x0, rs2
                            instr_o = {7'b0, instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], riscv::OpcodeOp};

                            if (instr_i[6:2] == 5'b0) begin
                                // c.jr -> jalr x0, rd/rs1, 0
                                instr_o = {12'b0, instr_i[11:7], 3'b0, 5'b0, riscv::OpcodeJalr};
                                // rs1 != 0
                                illegal_instr_o = (instr_i[11:7] != '0) ? 1'b0 : 1'b1;
                            end
                        end else begin
                            // c.add -> add rd, rd, rs2
                            instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], riscv::OpcodeOp};

                            if (instr_i[11:7] == 5'b0) begin
                                // c.ebreak -> ebreak
                                instr_o = {32'h00_10_00_73};
                                if (instr_i[6:2] != 5'b0)
                                    illegal_instr_o = 1'b1;
                            end else if (instr_i[6:2] == 5'b0) begin
                                // c.jalr -> jalr x1, rs1, 0
                                instr_o = {12'b0, instr_i[11:7], 3'b000, 5'b00001, riscv::OpcodeJalr};
                            end
                        end
                    end

                    riscv::OpcodeC2Fsdsp: begin
                        // c.fsdsp -> fsd rs2, imm(x2)
                        instr_o = {3'b0, instr_i[9:7], instr_i[12], instr_i[6:2], 5'h02, 3'b011, instr_i[11:10], 3'b000, riscv::OpcodeStoreFp};
                    end

                    riscv::OpcodeC2Swsp: begin
                        // c.swsp -> sw rs2, imm(x2)
                        instr_o = {4'b0, instr_i[8:7], instr_i[12], instr_i[6:2], 5'h02, 3'b010, instr_i[11:9], 2'b00, riscv::OpcodeStore};
                    end

                    riscv::OpcodeC2Sdsp: begin
                        // c.sdsp -> sd rs2, imm(x2)
                        instr_o = {3'b0, instr_i[9:7], instr_i[12], instr_i[6:2], 5'h02, 3'b011, instr_i[11:10], 3'b000, riscv::OpcodeStore};
                    end

                    default: begin
                        illegal_instr_o = 1'b1;
                    end
                endcase
            end

            // normal instruction
            default: is_compressed_o = 1'b0;
        endcase

        // Check if the instruction was illegal, if it was then output the offending instruction (zero-extended)
        if (illegal_instr_o && is_compressed_o) begin
            instr_o = instr_i;
        end
    end
endmodule
