// Author: Florian Zaruba, ETH Zurich
// Date: 16.05.2017
// Description: Instruction Tracer Defines
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

parameter INSTR_LUI       = { 25'b?, OPCODE_LUI };
parameter INSTR_AUIPC     = { 25'b?, OPCODE_AUIPC };
parameter INSTR_JAL       = { 25'b?, OPCODE_JAL };
parameter INSTR_JALR      = { 17'b?, 3'b000, 5'b?, OPCODE_JALR };
// BRANCH
parameter INSTR_BEQ      =  { 17'b?, 3'b000, 5'b?, OPCODE_BRANCH };
parameter INSTR_BNE      =  { 17'b?, 3'b001, 5'b?, OPCODE_BRANCH };
parameter INSTR_BLT      =  { 17'b?, 3'b100, 5'b?, OPCODE_BRANCH };
parameter INSTR_BGE      =  { 17'b?, 3'b101, 5'b?, OPCODE_BRANCH };
parameter INSTR_BLTU     =  { 17'b?, 3'b110, 5'b?, OPCODE_BRANCH };
parameter INSTR_BGEU     =  { 17'b?, 3'b111, 5'b?, OPCODE_BRANCH };

// OPIMM
parameter INSTR_ADDI     =  { 17'b?, 3'b000, 5'b?, OPCODE_OPIMM };
parameter INSTR_SLTI     =  { 17'b?, 3'b010, 5'b?, OPCODE_OPIMM };
parameter INSTR_SLTIU    =  { 17'b?, 3'b011, 5'b?, OPCODE_OPIMM };
parameter INSTR_XORI     =  { 17'b?, 3'b100, 5'b?, OPCODE_OPIMM };
parameter INSTR_ORI      =  { 17'b?, 3'b110, 5'b?, OPCODE_OPIMM };
parameter INSTR_ANDI     =  { 17'b?, 3'b111, 5'b?, OPCODE_OPIMM };
parameter INSTR_SLLI     =  { 7'b0000000, 10'b?, 3'b001, 5'b?, OPCODE_OPIMM };
parameter INSTR_SRLI     =  { 7'b0000000, 10'b?, 3'b101, 5'b?, OPCODE_OPIMM };
parameter INSTR_SRAI     =  { 7'b0100000, 10'b?, 3'b101, 5'b?, OPCODE_OPIMM };
// OP
parameter INSTR_ADD      =  { 7'b0000000, 10'b?, 3'b000, 5'b?, OPCODE_OP };
parameter INSTR_SUB      =  { 7'b0100000, 10'b?, 3'b000, 5'b?, OPCODE_OP };
parameter INSTR_SLL      =  { 7'b0000000, 10'b?, 3'b001, 5'b?, OPCODE_OP };
parameter INSTR_SLT      =  { 7'b0000000, 10'b?, 3'b010, 5'b?, OPCODE_OP };
parameter INSTR_SLTU     =  { 7'b0000000, 10'b?, 3'b011, 5'b?, OPCODE_OP };
parameter INSTR_XOR      =  { 7'b0000000, 10'b?, 3'b100, 5'b?, OPCODE_OP };
parameter INSTR_SRL      =  { 7'b0000000, 10'b?, 3'b101, 5'b?, OPCODE_OP };
parameter INSTR_SRA      =  { 7'b0100000, 10'b?, 3'b101, 5'b?, OPCODE_OP };
parameter INSTR_OR       =  { 7'b0000000, 10'b?, 3'b110, 5'b?, OPCODE_OP };
parameter INSTR_AND      =  { 7'b0000000, 10'b?, 3'b111, 5'b?, OPCODE_OP };
// FENCE
parameter INSTR_FENCE    =  { 4'b0, 8'b?, 13'b0, OPCODE_FENCE };
parameter INSTR_FENCEI   =  { 17'b0, 3'b001, 5'b0, OPCODE_FENCE };
// SYSTEM
parameter INSTR_CSRRW    =  { 17'b?, 3'b001, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRS    =  { 17'b?, 3'b010, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRC    =  { 17'b?, 3'b011, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRWI   =  { 17'b?, 3'b101, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRSI   =  { 17'b?, 3'b110, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRCI   =  { 17'b?, 3'b111, 5'b?, OPCODE_SYSTEM };
parameter INSTR_ECALL    =  { 12'b000000000000, 13'b0, OPCODE_SYSTEM };
parameter INSTR_EBREAK   =  { 12'b000000000001, 13'b0, OPCODE_SYSTEM };
parameter INSTR_ERET     =  { 12'b000100000000, 13'b0, OPCODE_SYSTEM };
parameter INSTR_WFI      =  { 12'b000100000010, 13'b0, OPCODE_SYSTEM };

// RV32M
parameter INSTR_PMUL     =  { 7'b0000001, 10'b?, 3'b000, 5'b?, OPCODE_OP };
parameter INSTR_DIV      =  { 7'b0000001, 10'b?, 3'b100, 5'b?, OPCODE_OP };
parameter INSTR_DIVU     =  { 7'b0000001, 10'b?, 3'b101, 5'b?, OPCODE_OP };
parameter INSTR_REM      =  { 7'b0000001, 10'b?, 3'b110, 5'b?, OPCODE_OP };
parameter INSTR_REMU     =  { 7'b0000001, 10'b?, 3'b111, 5'b?, OPCODE_OP };

// Load/Stores
parameter INSTR_LOAD     =  {25'b?, OPCODE_LOAD};
parameter INSTR_STORE    =  {25'b?, OPCODE_STORE};