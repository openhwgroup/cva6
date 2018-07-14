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
// Author: Florian Zaruba, ETH Zurich
// Date: 16.05.2017
// Description: Instruction Tracer Defines

parameter INSTR_LUI       = { 25'b?, OpcodeLui };
parameter INSTR_AUIPC     = { 25'b?, OpcodeAuipc };
parameter INSTR_JAL       = { 25'b?, OpcodeJal };
parameter INSTR_JALR      = { 17'b?, 3'b000, 5'b?, OpcodeJalr };
// BRANCH
parameter INSTR_BEQZ     =  { 7'b?, 5'b0, 5'b?, 3'b000, 5'b?, OpcodeBranch };
parameter INSTR_BEQ      =  { 7'b?, 5'b?, 5'b?, 3'b000, 5'b?, OpcodeBranch };
parameter INSTR_BNEZ     =  { 7'b?, 5'b0, 5'b?, 3'b001, 5'b?, OpcodeBranch };
parameter INSTR_BNE      =  { 7'b?, 5'b?, 5'b?, 3'b001, 5'b?, OpcodeBranch };
parameter INSTR_BLTZ     =  { 7'b?, 5'b0, 5'b?, 3'b100, 5'b?, OpcodeBranch };
parameter INSTR_BLT      =  { 7'b?, 5'b?, 5'b?, 3'b100, 5'b?, OpcodeBranch };
parameter INSTR_BGEZ     =  { 7'b?, 5'b0, 5'b?, 3'b101, 5'b?, OpcodeBranch };
parameter INSTR_BGE      =  { 7'b?, 5'b?, 5'b?, 3'b101, 5'b?, OpcodeBranch };
parameter INSTR_BLTU     =  { 7'b?, 5'b?, 5'b?, 3'b110, 5'b?, OpcodeBranch };
parameter INSTR_BGEU     =  { 7'b?, 5'b?, 5'b?, 3'b111, 5'b?, OpcodeBranch };

// OPIMM
parameter INSTR_LI       =  { 12'b?, 5'b0, 3'b000, 5'b?, OpcodeOpimm };
parameter INSTR_ADDI     =  { 17'b?, 3'b000, 5'b?, OpcodeOpimm };
parameter INSTR_SLTI     =  { 17'b?, 3'b010, 5'b?, OpcodeOpimm };
parameter INSTR_SLTIU    =  { 17'b?, 3'b011, 5'b?, OpcodeOpimm };
parameter INSTR_XORI     =  { 17'b?, 3'b100, 5'b?, OpcodeOpimm };
parameter INSTR_ORI      =  { 17'b?, 3'b110, 5'b?, OpcodeOpimm };
parameter INSTR_ANDI     =  { 17'b?, 3'b111, 5'b?, OpcodeOpimm };
parameter INSTR_SLLI     =  { 6'b000000, 11'b?, 3'b001, 5'b?, OpcodeOpimm };
parameter INSTR_SRLI     =  { 6'b000000, 11'b?, 3'b101, 5'b?, OpcodeOpimm };
parameter INSTR_SRAI     =  { 6'b010000, 11'b?, 3'b101, 5'b?, OpcodeOpimm };

// OPIMM32
parameter INSTR_ADDIW    =  { 17'b?, 3'b000, 5'b?, OpcodeOpimm32 };
parameter INSTR_SLLIW    =  { 7'b0000000, 10'b?, 3'b001, 5'b?, OpcodeOpimm32 };
parameter INSTR_SRLIW    =  { 7'b0000000, 10'b?, 3'b101, 5'b?, OpcodeOpimm32 };
parameter INSTR_SRAIW    =  { 7'b0100000, 10'b?, 3'b101, 5'b?, OpcodeOpimm32 };

// OP
parameter INSTR_ADD      =  { 7'b0000000, 10'b?, 3'b000, 5'b?, OpcodeOp };
parameter INSTR_SUB      =  { 7'b0100000, 10'b?, 3'b000, 5'b?, OpcodeOp };
parameter INSTR_SLL      =  { 7'b0000000, 10'b?, 3'b001, 5'b?, OpcodeOp };
parameter INSTR_SLT      =  { 7'b0000000, 10'b?, 3'b010, 5'b?, OpcodeOp };
parameter INSTR_SLTU     =  { 7'b0000000, 10'b?, 3'b011, 5'b?, OpcodeOp };
parameter INSTR_XOR      =  { 7'b0000000, 10'b?, 3'b100, 5'b?, OpcodeOp };
parameter INSTR_SRL      =  { 7'b0000000, 10'b?, 3'b101, 5'b?, OpcodeOp };
parameter INSTR_SRA      =  { 7'b0100000, 10'b?, 3'b101, 5'b?, OpcodeOp };
parameter INSTR_OR       =  { 7'b0000000, 10'b?, 3'b110, 5'b?, OpcodeOp };
parameter INSTR_AND      =  { 7'b0000000, 10'b?, 3'b111, 5'b?, OpcodeOp };
parameter INSTR_MUL      =  { 7'b0000001, 10'b?, 3'b???, 5'b?, OpcodeOp };

// OP32
parameter INSTR_ADDW     =  { 7'b0000000, 10'b?, 3'b000, 5'b?, OpcodeOp32 };
parameter INSTR_SUBW     =  { 7'b0100000, 10'b?, 3'b000, 5'b?, OpcodeOp32 };
parameter INSTR_SLLW     =  { 7'b0000000, 10'b?, 3'b001, 5'b?, OpcodeOp32 };
parameter INSTR_SRLW     =  { 7'b0000000, 10'b?, 3'b101, 5'b?, OpcodeOp32 };
parameter INSTR_SRAW     =  { 7'b0100000, 10'b?, 3'b101, 5'b?, OpcodeOp32 };
parameter INSTR_MULW     =  { 7'b0000001, 10'b?, 3'b???, 5'b?, OpcodeOp32 };

// FENCE
parameter INSTR_FENCE    =  { 4'b0, 8'b?, 13'b0, OpcodeFence };
parameter INSTR_FENCEI   =  { 17'b0, 3'b001, 5'b0, OpcodeFence };
// SYSTEM
parameter INSTR_CSRW     =  { 12'b?, 5'b?, 3'b001, 5'b0, OpcodeSystem };
parameter INSTR_CSRRW    =  { 12'b?, 5'b?, 3'b001, 5'b?, OpcodeSystem };
parameter INSTR_CSRR     =  { 12'b?, 5'b0, 3'b010, 5'b?, OpcodeSystem };
parameter INSTR_CSRRS    =  { 12'b?, 5'b?, 3'b010, 5'b?, OpcodeSystem };
parameter INSTR_CSRS     =  { 12'b?, 5'b?, 3'b010, 5'b0, OpcodeSystem };
parameter INSTR_CSRRC    =  { 12'b?, 5'b?, 3'b011, 5'b?, OpcodeSystem };
parameter INSTR_CSRC     =  { 12'b?, 5'b?, 3'b011, 5'b0, OpcodeSystem };

parameter INSTR_CSRWI    =  { 17'b?, 3'b101, 5'b0, OpcodeSystem };
parameter INSTR_CSRRWI   =  { 17'b?, 3'b101, 5'b?, OpcodeSystem };
parameter INSTR_CSRSI    =  { 17'b?, 3'b110, 5'b0, OpcodeSystem };
parameter INSTR_CSRRSI   =  { 17'b?, 3'b110, 5'b?, OpcodeSystem };
parameter INSTR_CSRCI    =  { 17'b?, 3'b111, 5'b0, OpcodeSystem };
parameter INSTR_CSRRCI   =  { 17'b?, 3'b111, 5'b?, OpcodeSystem };

parameter INSTR_ECALL    =  { 12'b000000000000, 13'b0, OpcodeSystem };
parameter INSTR_EBREAK   =  { 12'b000000000001, 13'b0, OpcodeSystem };
parameter INSTR_MRET     =  { 12'b001100000010, 13'b0, OpcodeSystem };
parameter INSTR_SRET     =  { 12'b000100000010, 13'b0, OpcodeSystem };
parameter INSTR_DRET     =  { 12'b011110110010, 13'b0, OpcodeSystem };
parameter INSTR_WFI      =  { 12'b000100000101, 13'b0, OpcodeSystem };
parameter INSTR_SFENCE   =  { 12'b0001001?????, 13'b?, OpcodeSystem };

// RV32M
parameter INSTR_PMUL     =  { 7'b0000001, 10'b?, 3'b000, 5'b?, OpcodeOp };
parameter INSTR_DIV      =  { 7'b0000001, 10'b?, 3'b100, 5'b?, OpcodeOp };
parameter INSTR_DIVU     =  { 7'b0000001, 10'b?, 3'b101, 5'b?, OpcodeOp };
parameter INSTR_REM      =  { 7'b0000001, 10'b?, 3'b110, 5'b?, OpcodeOp };
parameter INSTR_REMU     =  { 7'b0000001, 10'b?, 3'b111, 5'b?, OpcodeOp };

// Load/Stores
parameter INSTR_LOAD     =  {25'b?, OpcodeLoad };
parameter INSTR_STORE    =  {25'b?, OpcodeStore };
