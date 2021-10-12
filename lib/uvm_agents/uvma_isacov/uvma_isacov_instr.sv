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



class uvma_isacov_instr_c extends uvm_object;

  instr_name_t  name;
  instr_ext_t   ext;
  instr_type_t  itype;
  instr_group_t group;
  instr_csr_t   csr;
  bit           illegal;

  bit[31:0] pc;
  bit[31:0] mem_addr;

  bit [11:0]  csr_val;
  bit [4:0]   rs1;
  bit [4:0]   rs2;
  bit [4:0]   rd;
  bit [11:0]  immi;
  bit [11:0]  imms;
  bit [12:1]  immb;
  bit [31:12] immu;
  bit [20:1]  immj;

  // Valid flags for fields (to calculate hazards and other coverage)
  bit rs1_valid;
  bit rs2_valid;
  bit rd_valid;

  bit [31:0] c_imm;
  bit [5:0]  c_rdrs1;
  bit [5:0]  c_rs1s;
  bit [5:0]  c_rs2s;
  bit [5:0]  c_rdp;

  bit[31:0]     rs1_value;
  instr_value_t rs1_value_type;
  bit[31:0]     rs2_value;
  instr_value_t rs2_value_type;
  bit[31:0]     rd_value;
  instr_value_t rd_value_type;

  instr_value_t immi_value_type;
  instr_value_t imms_value_type;
  instr_value_t immb_value_type;
  instr_value_t immu_value_type;
  instr_value_t immj_value_type;

  instr_value_t c_imm_value_type;

  `uvm_object_utils_begin(uvma_isacov_instr_c);
    `uvm_field_enum(instr_name_t,  name, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_ext_t,   ext, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_type_t,  itype, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_group_t, group, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_csr_t,   csr, UVM_ALL_ON | UVM_NOPRINT);

    `uvm_field_int(illegal,   UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(csr_val,   UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs1,       UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs1_value, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs1_valid, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, rs1_value_type, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs2,       UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs2_value, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs2_valid, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, rs2_value_type, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rd,        UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rd_value,  UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rd_valid,  UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, rd_value_type, UVM_ALL_ON | UVM_NOPRINT);

    `uvm_field_int(immi, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, immi_value_type, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(imms, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, imms_value_type, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(immb, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, immb_value_type, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(immu, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, immu_value_type, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(immj, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, immj_value_type, UVM_ALL_ON | UVM_NOPRINT);

    `uvm_field_int(c_imm,    UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_value_t, c_imm_value_type, UVM_ALL_ON | UVM_NOPRINT);

  `uvm_object_utils_end;

  extern function new(string name = "isacov_instr");

  extern function string convert2string();

  extern function void set_valid_flags();
  extern function bit is_csr_write();
  extern function bit is_conditional_branch();
  extern function bit is_branch_taken();

  extern function instr_value_t get_instr_value_type(bit[31:0] value, int unsigned width, bit is_signed);

endclass : uvma_isacov_instr_c

function uvma_isacov_instr_c::new(string name = "isacov_instr");
  super.new(name);
endfunction : new

function string uvma_isacov_instr_c::convert2string();
  // Printing for a few special-formatting cases
  if (name inside {LW, LH, LB, LHU, LBU}) begin
    return $sformatf("0x%08x %s x%0d, %0d(x%0d)", pc, name.name().tolower(), rd, $signed(immi), rs1);
  end
  if (name inside {SLLI, SRLI, SRAI}) begin
    return $sformatf("0x%08x %s x%0d, x%0d, 0x%0x", pc, name.name().tolower(), rd, rs1, rs2);
  end
  if (name == FENCE_I) begin
    return $sformatf("0x%08x fence.i", pc);
  end

  // Printing based on instruction format type
  if (itype == R_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d, x%0d", pc, name.name().tolower(), rd, rs1, rs2);
  end
  if (itype == I_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d, %0d", pc, name.name().tolower(), rd, rs1, $signed(immi));
  end
  if (itype == S_TYPE) begin
    return $sformatf("0x%08x %s x%0d, %0d(x%0d)", pc, name.name().tolower(), rs2, $signed(imms), rs1);
  end
  if (itype == B_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d, %0d", pc, name.name().tolower(), rs1, rs2, $signed({immb, 1'b0}));
  end
  if (itype == U_TYPE) begin
    return $sformatf("0x%08x %s x%0d, 0x%0x", pc, name.name().tolower(), rd, {immu, 12'd0});
  end
  if (itype == J_TYPE) begin
    return $sformatf("0x%08x %s x%0d, %0d", pc, name.name().tolower(), rd, $signed(immj));
  end
  if (itype == CSR_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d, %s", pc, name.name().tolower(), rd, rs1, csr.name().tolower());
  end
  if (itype == CSRI_TYPE) begin
    return $sformatf("0x%08x %s x%0d, %0d, %s", pc, name.name().tolower(), rd, rs1, csr.name().tolower());
  end
  if (itype == CI_TYPE) begin
    return $sformatf("0x%08x %s x%0d, %0d", pc, name.name().tolower(), rd, c_imm);
  end
  if (itype == CR_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d", pc, name.name().tolower(), rd, rs2);
  end
  if (itype == CSS_TYPE) begin
    return $sformatf("0x%08x %s x%0d, %0d", pc, name.name().tolower(), rs2, c_imm);
  end
  if (itype == CIW_TYPE) begin
    return $sformatf("0x%08x %s x%0d, %0d", pc, name.name().tolower(), rd, c_imm);
  end
  if (itype == CL_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d, %0d", pc, name.name().tolower(), rd, rs1, c_imm);
  end
  if (itype == CS_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d, %0d", pc, name.name().tolower(), rs1, rs2, c_imm);
  end
  if (itype == CA_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d", pc, name.name().tolower(), rd, rs2);
  end
  if (itype == CB_TYPE) begin
    return $sformatf("0x%08x %s x%0d, x%0d", pc, name.name().tolower(), rd, rs2);
  end
  if (itype == CJ_TYPE) begin
    return $sformatf("0x%08x %s x%0d", pc, name.name().tolower(), c_imm);
  end

  // Default printing of just the instruction name
  return $sformatf("0x%08x %s", pc, name.name().tolower());

endfunction : convert2string

function void uvma_isacov_instr_c::set_valid_flags();
  if (itype == R_TYPE) begin
    rs1_valid = 1;
    rs2_valid = 1;
    rd_valid = 1;
    return;
  end

  if (itype == I_TYPE) begin
    rs1_valid = 1;
    rd_valid = 1;
    return;
  end

  if (itype == S_TYPE) begin
    rs1_valid = 1;
    rs2_valid = 1;
    return;
  end

  if (itype == B_TYPE) begin
    rs1_valid = 1;
    rs2_valid = 1;
    return;
  end

  if (itype == U_TYPE) begin
    rd_valid = 1;
    return;
  end

  if (itype == J_TYPE) begin
    rd_valid = 1;
    return;
  end

  if (itype == CI_TYPE) begin
    rd_valid = 1;
    return;
  end

  if (itype == CR_TYPE) begin
    rs1_valid = 1;
    rs2_valid = 1;
    rd_valid = 1;
    return;
  end

  if (itype == CSS_TYPE) begin
    rs2_valid = 1;
    return;
  end

  if (itype == CIW_TYPE) begin
    rd_valid = 1;
    return;
  end

  if (itype == CL_TYPE) begin
    rs1_valid = 1;
    rd_valid = 1;
    return;
  end

  if (itype == CS_TYPE) begin
    rs1_valid = 1;
    rs2_valid = 1;
    return;
  end

  if (itype == CA_TYPE) begin
    rs1_valid = 1;
    rs2_valid = 1;
    rd_valid = 1;
    return;
  end

  if (itype == CB_TYPE) begin
    rs1_valid = 1;
    return;
  end

  if (itype == CSR_TYPE) begin
    rs1_valid = 1;
    rd_valid = 1;
    return;
  end

  if (itype == CSRI_TYPE) begin
    rd_valid = 1;
    return;
  end

  if (itype == CSRI_TYPE) begin
    rd_valid = 1;
    return;
  end

endfunction : set_valid_flags

function bit uvma_isacov_instr_c::is_csr_write();
  // Using Table 9.1 in RISC-V specification to define a CSR write
  if (name inside {CSRRW})
    return 1;

  if (name inside {CSRRS, CSRRC} && rs1 != 0)
    return 1;

  if (name inside {CSRRWI})
    return 1;

  if (name inside {CSRRSI, CSRRCI} && immu != 0)
    return 1;

  return 0;
endfunction : is_csr_write

function instr_value_t uvma_isacov_instr_c::get_instr_value_type(bit[31:0] value, int unsigned width, bit is_signed);
  if (value == 0)
    return ZERO;

  if (is_signed)
    return value[width-1] ? NEGATIVE : POSITIVE;

  return NON_ZERO;

endfunction : get_instr_value_type

function bit uvma_isacov_instr_c::is_conditional_branch();

  if (name inside {BEQ, BNE, BLT, BGE, BLTU, BGEU, C_BEQZ, C_BNEZ})
    return 1;

  return 0;

endfunction : is_conditional_branch


function bit uvma_isacov_instr_c::is_branch_taken();

  case (name)
    BEQ:  return (rs1_value == rs2_value) ? 1 : 0;
    BNE:  return (rs1_value != rs2_value) ? 1 : 0;
    BLT:  return ($signed(rs1_value) <  $signed(rs2_value)) ? 1 : 0;
    BGE:  return ($signed(rs1_value) >= $signed(rs2_value)) ? 1 : 0;
    BLTU: return (rs1_value <  rs2_value) ? 1 : 0;
    BGEU: return (rs1_value >= rs2_value) ? 1 : 0;
    C_BEQZ: return (!rs1_value) ? 1 : 0;
    C_BNEZ: return (rs1_value)  ? 1 : 0;
  endcase

  `uvm_fatal("ISACOVBRANCH", $sformatf("Called is_branch_taken for non-branch instruction: %s", name.name()));

endfunction : is_branch_taken

