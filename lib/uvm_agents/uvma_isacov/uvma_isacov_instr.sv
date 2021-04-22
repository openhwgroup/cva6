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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


typedef enum {
  UNKNOWN,  // TODO this should not be needed?

  // 32I
  LUI, AUIPC, JAL, JALR,
  BEQ, BNE, BLT, BGE, BLTU, BGEU,
  LB, LH, LW, LBU, LHU, SB, SH, SW,
  ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI,
  ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND,
  FENCE, ECALL, EBREAK, DRET, MRET, WFI,

  // 32M
  MUL, MULH, MULHSU, MULHU,
  DIV, DIVU, REM, REMU,

  // 32C
  C_ADDI4SPN, C_LW, C_SW,
  C_ADDI, C_JAL, C_LI, C_ADDI16SP, C_LUI, C_SRLI, C_SRAI,
  C_ANDI, C_SUB, C_XOR, C_OR, C_AND, C_J, C_BEQZ, C_BNEZ,
  C_SLLI, C_LWSP, C_JR, C_MV, C_EBREAK, C_JALR, C_ADD, C_SWSP,

  // Zicsr
  CSRRW, CSRRS, CSRRC,
  CSRRWI, CSRRSI, CSRRCI,

  // Zifencei
  FENCE_I
} instr_name_t;

typedef enum {
  // RV32 types
  R_TYPE,
  I_TYPE,
  S_TYPE,
  B_TYPE,
  U_TYPE,
  J_TYPE,

  UNKNOWN_TYPE // Delete when all are implemented
} instr_type_t;

class uvma_isacov_instr_c extends uvm_object;
  
  instr_name_t name;

  bit [4:0] rs1;
  bit [4:0] rs2;
  bit [4:0] rd;
  bit [11:0] immi;
  bit [11:0] imms;
  bit [12:1] immb;
  bit [19:0] immu;
  bit [20:1] immj;

  bit [2:0] c_rs1p;
  bit [2:0] c_rs2p;
  bit [2:0] c_rdp;
  bit [4:0] c_rdrs1;  // rd/rs1
  bit [4:0] c_rs2;
  bit [2:0] c_rdprs1p;  // rd'/rs1'
  bit [7:0] c_immiw;
  bit [5:0] c_imml;
  bit [5:0] c_imms;
  bit [11:1] c_immj;
  bit [5:0] c_immi;
  bit [7:0] c_immb;
  bit [5:0] c_immss;

  `uvm_object_utils_begin(uvma_isacov_instr_c);
    `uvm_field_enum(instr_name_t, name, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs1, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs2, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rd, UVM_ALL_ON | UVM_NOPRINT);

    `uvm_field_int(immi, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(imms, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(immb, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(immu, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(immj, UVM_ALL_ON | UVM_NOPRINT);

    `uvm_field_int(c_rs1p,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_rs2p,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_rdp,     UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_rdrs1,   UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_rs2,     UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_rdprs1p, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_immiw,   UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_imml,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_imms,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_immj,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_immj,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_immi,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_immb,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_immss,   UVM_ALL_ON | UVM_NOPRINT);    
  `uvm_object_utils_end;

  extern function new(string name = "isacov_instr");

  extern function string convert2string();

  extern function instr_type_t get_instr_type();
endclass : uvma_isacov_instr_c

function uvma_isacov_instr_c::new(string name = "isacov_instr");
  super.new(name);
endfunction : new

function instr_type_t uvma_isacov_instr_c::get_instr_type();
  if (name inside {ADD,SUB,SLL,SLT,SLTU,XOR,SRL,SRA,OR,AND}) 
    return R_TYPE;

  return UNKNOWN_TYPE;
endfunction : get_instr_type

function string uvma_isacov_instr_c::convert2string();
  instr_type_t instr_type = this.get_instr_type();

  if (instr_type == R_TYPE) begin
    return $sformatf("%s x%0d, x%0d, x%0d", name.name(), rd, rs1, rs2);
  end

  return name.name();
endfunction : convert2string
