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
    assign rvi_imm_o    = (instr_i[3]) ? uj_imm(instr_i) : sb_imm(instr_i);
    assign rvi_branch_o = (instr_i[6:0] == riscv::OpcodeBranch) ? 1'b1 : 1'b0;
    assign rvi_jalr_o   = (instr_i[6:0] == riscv::OpcodeJalr)   ? 1'b1 : 1'b0;
    assign rvi_jump_o   = (instr_i[6:0] == riscv::OpcodeJal)    ? 1'b1 : 1'b0;
    // opcode JAL
    assign rvc_jump_o   = (instr_i[15:13] == riscv::OpcodeCJ) & is_rvc_o & (instr_i[1:0] == 2'b01);
    assign rvc_jr_o     = (instr_i[15:12] == 4'b1000) & (instr_i[6:2] == 5'b00000) & is_rvc_o & (instr_i[1:0] == 2'b10);
    assign rvc_branch_o = ((instr_i[15:13] == riscv::OpcodeCBeqz) | (instr_i[15:13] == riscv::OpcodeCBnez)) & is_rvc_o & (instr_i[1:0] == 2'b01);
    // check that rs1 is x1 or x5
    assign rvc_return_o = rvc_jr_o & ~instr_i[11] & ~instr_i[10] & ~instr_i[8] & instr_i[7];
    assign rvc_jalr_o   = (instr_i[15:12] == 4'b1001) & (instr_i[6:2] == 5'b00000) & is_rvc_o;
    assign rvc_call_o   = rvc_jalr_o;  // TODO: check that this captures calls

    // // differentiates between JAL and BRANCH opcode, JALR comes from BHT
    assign rvc_imm_o    = (instr_i[14]) ? {{56{instr_i[12]}}, instr_i[6:5], instr_i[2], instr_i[11:10], instr_i[4:3], 1'b0}
                                       : {{53{instr_i[12]}}, instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], 1'b0};
endmodule
