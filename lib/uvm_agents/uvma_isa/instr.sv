// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


typedef enum {
  UNKNOWN,

  // 32I
  LUI, AUIPC, JAL, JALR,
  BEQ, BNE, BLT, BGE, BLTU, BGEU,
  LB, LH, LW, LBU, LHU, SB, SH, SW,
  ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI,
  ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND,
  FENCE, ECALL, EBREAK,

  // 32M
  MULH, DIVU,

  // 32C
  C_J, C_JAL,
  C_BEQZ, C_BNEZ,

  // Zicsr
  CSRRW, CSRRS, CSRRC,
  CSRRWI, CSRRSI, CSRRCI,

  // Zifencei
  FENCE_I
} instr_name_t;


class instr_c extends uvm_object;

  instr_name_t name;

  bit [4:0] rs1;
  bit [4:0] rs2;
  bit [4:0] rd;
  bit [11:0] immi;
  bit [11:0] imms;
  bit [12:1] immb;
  bit [19:0] immu;
  bit [20:1] immj;

  bit [11:1] c_immj;

endclass : instr_c
