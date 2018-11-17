//Copyright (C) 2018 to present,
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// Author: Florian Zaruba, ETH Zurich
// Date: 08.02.2018
// Migrated: Luis Vitorio Cargnini, IEEE
// Date: 09.06.2018

// ------------------------------
// Instruction Scanner
// ------------------------------
module instr_scan (
    input  logic [31:0] instr_i,        // expect aligned instruction, compressed or not
    output logic        is_rvc_o,
    output logic        rvi_return_o,
    output logic        rvi_call_o,
    output logic        rvi_branch_o,
    output logic        rvi_jalr_o,
    output logic        rvi_jump_o,
    output logic [63:0] rvi_imm_o,
    output logic        rvc_branch_o,
    output logic        rvc_jump_o,
    output logic        rvc_jr_o,
    output logic        rvc_return_o,
    output logic        rvc_jalr_o,
    output logic        rvc_call_o,
    output logic [63:0] rvc_imm_o
);
    assign is_rvc_o     = (instr_i[1:0] != 2'b11);
    // check that rs1 is either x1 or x5 and that rs1 is not x1 or x5, TODO: check the fact about bit 7
    assign rvi_return_o = rvi_jalr_o & ~instr_i[7] & ~instr_i[19] & ~instr_i[18] & ~instr_i[16] & instr_i[15];
    assign rvi_call_o   = (rvi_jalr_o | rvi_jump_o) & instr_i[7]; // TODO: check that this captures calls
    // differentiates between JAL and BRANCH opcode, JALR comes from BHT
    assign rvi_imm_o    = (instr_i[3]) ? ariane_pkg::uj_imm(instr_i) : ariane_pkg::sb_imm(instr_i);
    assign rvi_branch_o = (instr_i[6:0] == riscv::OpcodeBranch) ? 1'b1 : 1'b0;
    assign rvi_jalr_o   = (instr_i[6:0] == riscv::OpcodeJalr)   ? 1'b1 : 1'b0;
    assign rvi_jump_o   = (instr_i[6:0] == riscv::OpcodeJal)    ? 1'b1 : 1'b0;
    // opcode JAL
    assign rvc_jump_o   = (instr_i[15:13] == riscv::OpcodeC1J) & is_rvc_o & (instr_i[1:0] == riscv::OpcodeC1);
    // always links to register 0
    assign rvc_jr_o     = (instr_i[15:13] == riscv::OpcodeC2JalrMvAdd)
                        & ~instr_i[12]
                        & (instr_i[6:2] == 5'b00000)
                        & (instr_i[1:0] == riscv::OpcodeC2)
                        & is_rvc_o;
    assign rvc_branch_o = ((instr_i[15:13] == riscv::OpcodeC1Beqz) | (instr_i[15:13] == riscv::OpcodeC1Bnez))
                        & (instr_i[1:0] == riscv::OpcodeC1)
                        & is_rvc_o;
    // check that rs1 is x1 or x5
    assign rvc_return_o = ~instr_i[11] & ~instr_i[10] & ~instr_i[8] & instr_i[7] & rvc_jr_o ;
    // always links to register 1 e.g.: it is a jump
    assign rvc_jalr_o   = (instr_i[15:13] == riscv::OpcodeC2JalrMvAdd)
                        & instr_i[12]
                        & (instr_i[6:2] == 5'b00000) & is_rvc_o;
    assign rvc_call_o   = rvc_jalr_o;

    // // differentiates between JAL and BRANCH opcode, JALR comes from BHT
    assign rvc_imm_o    = (instr_i[14]) ? {{56{instr_i[12]}}, instr_i[6:5], instr_i[2], instr_i[11:10], instr_i[4:3], 1'b0}
                                       : {{53{instr_i[12]}}, instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], 1'b0};
endmodule
