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



class uvma_isacov_instr_c#(int ILEN=DEFAULT_ILEN,
                           int XLEN=DEFAULT_XLEN) extends uvm_object;

  // Set for illegal instructions
  bit           illegal;

  // Set for traped instructions, determines what should not be considered for coverage
  bit [13:0]    trap;

  // Enumeration
  instr_name_t  name;
  instr_ext_t   ext;
  instr_type_t  itype;
  instr_group_t group;
  instr_csr_t   csr;

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

  // rx for compressed instruction (5-bit encoding)
  bit [4:0]  c_rdrs1;

  // rx for compressed instruction (3-bit encoding)
  bit [2:0]  c_rs1;
  bit [2:0]  c_rs2;
  bit [2:0]  c_rd;

  bit[XLEN-1:0]     rs1_value;
  instr_value_t rs1_value_type;
  bit[XLEN-1:0]     rs2_value;
  instr_value_t rs2_value_type;
  bit[XLEN-1:0]     rd_value;
  instr_value_t rd_value_type;

  instr_value_t immi_value_type;
  instr_value_t imms_value_type;
  instr_value_t immb_value_type;
  instr_value_t immu_value_type;
  instr_value_t immj_value_type;

  instr_value_t c_imm_value_type;

  uvma_rvfi_instr_seq_item_c#(ILEN, XLEN) rvfi;

  `uvm_object_param_utils_begin(uvma_isacov_instr_c#(ILEN,XLEN));
    `uvm_field_enum(instr_name_t,  name, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_ext_t,   ext, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_type_t,  itype, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_group_t, group, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_csr_t,   csr, UVM_ALL_ON | UVM_NOPRINT);

    `uvm_field_int(illegal,   UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(trap,      UVM_ALL_ON | UVM_NOPRINT);
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

    `uvm_field_int(c_rdrs1,     UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_rs1,       UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_rs2,       UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(c_rd,        UVM_ALL_ON | UVM_NOPRINT);

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

    `uvm_field_enum(instr_value_t, c_imm_value_type, UVM_ALL_ON | UVM_NOPRINT);

  `uvm_object_utils_end;

  extern function new(string name = "isacov_instr");

  extern function string convert2string();

  extern function void set_valid_flags();
  extern function bit is_csr_write();
  extern function bit is_conditional_branch();
  extern function bit is_branch_taken();

  extern function instr_value_t              get_instr_value_type(bit[XLEN-1:0] value, int unsigned width, bit is_signed);
  extern function int                        get_field_rd();
  extern function int                        get_field_rs1();
  extern function int                        get_field_rs2();
  extern function int                        get_field_imm();
  extern function int                        get_addr_rd();
  extern function int                        get_addr_rs1();
  extern function int                        get_addr_rs2();
  extern function int                        get_data_imm();
  
  extern function int                        decode_rd_c(bit[ILEN-1:0] instr);
  extern function int                        decode_rs1_c(bit[ILEN-1:0] instr);
  extern function int                        decode_rs2_c(bit[ILEN-1:0] instr);

endclass : uvma_isacov_instr_c


function uvma_isacov_instr_c::new(string name = "isacov_instr");
  super.new(name);
endfunction : new


function string uvma_isacov_instr_c::convert2string();

  string instr_str;

  // Printing based on instruction format type
  if (itype == R_TYPE) begin
    instr_str = $sformatf("x%0d, x%0d, x%0d",  rd, rs1, rs2);
  end
  if (itype == I_TYPE) begin
    instr_str = $sformatf("x%0d, x%0d, %0d",  rd, rs1, $signed(immi));
  end
  if (itype == S_TYPE) begin
    instr_str = $sformatf("x%0d, %0d(x%0d)",  rs2, $signed(imms), rs1);
  end
  if (itype == B_TYPE) begin
    instr_str = $sformatf("x%0d, x%0d, %0x",  rs1, rs2, ($signed(rvfi.pc_rdata) + $signed({immb, 1'b0})));
  end
  if (itype == U_TYPE) begin
    instr_str = $sformatf("x%0d, 0x%0x",  rd, immu);
  end
  if (itype == J_TYPE) begin
    instr_str = $sformatf("x%0d, %0x", rd, ($signed(rvfi.pc_rdata) + $signed({immj, 1'b0})));
  end
  if (itype == CSR_TYPE) begin
    instr_str = $sformatf("x%0d, %s, x%0d",  rd, csr.name().tolower(), rs1);
  end
  if (itype == CSRI_TYPE) begin
    instr_str = $sformatf("x%0d, %s, %0d",  rd, csr.name().tolower(), rs1);
  end
  if (itype == CI_TYPE) begin
    instr_str = $sformatf("x%0d, %0d",  this.get_addr_rd(), $signed(this.get_data_imm()));
  end
  if (itype == CR_TYPE) begin
    instr_str = $sformatf("x%0d, x%0d", this.get_addr_rd(), this.get_addr_rs2());
  end
  if (itype == CSS_TYPE) begin
    instr_str = $sformatf("x%0d, %0d(x2)",  this.get_addr_rs2(), this.get_data_imm());
  end
  if (itype == CIW_TYPE) begin
    instr_str = $sformatf("x%0d, x2, %0d", this.decode_rd_c($signed(this.rvfi.insn)), this.get_data_imm());
  end
  if (itype == CL_TYPE) begin
    instr_str = $sformatf("x%0d, %0d(x%0d)", this.decode_rd_c($signed(this.rvfi.insn)), this.get_data_imm(), this.decode_rs1_c($signed(this.rvfi.insn)));
  end
  if (itype == CS_TYPE) begin
    instr_str = $sformatf("x%0d, %0d(x%0d)", this.decode_rs2_c($signed(this.rvfi.insn)), this.get_data_imm(), this.decode_rs1_c($signed(this.rvfi.insn)));
  end
  if (itype == CA_TYPE) begin
    instr_str = $sformatf("x%0d, x%0d", this.decode_rs1_c($signed(this.rvfi.insn)), this.decode_rs2_c($signed(this.rvfi.insn)));
  end
  if (itype == CB_TYPE) begin
    instr_str = $sformatf("x%0d, %0x", this.decode_rs1_c($signed(this.rvfi.insn)), ($signed(rvfi.pc_rdata) + this.get_data_imm()));
  end
  if (itype == CJ_TYPE) begin
    instr_str = $sformatf("%0x", ($signed(rvfi.pc_rdata) + this.get_data_imm()));
  end
  // Special printing for a select few instructions:
  if (name inside {LW, LH, LB, LHU, LBU, JALR}) begin
    instr_str = $sformatf("x%0d, %0d(x%0d)", rd, $signed(immi), rs1);
  end
  if (name inside {SLLI, SRLI, SRAI}) begin
    instr_str = $sformatf("x%0d, x%0d, 0x%0x", rd, rs1, rs2);
  end
  if (name inside {C_LUI}) begin
    instr_str = $sformatf("x%0d, 0x%0x", this.get_addr_rd(), this.get_data_imm());
  end
  if (name inside {C_LWSP}) begin
    instr_str = $sformatf("x%0d, %0d(x2)", this.get_addr_rd(), this.get_data_imm());
  end
  if (name inside {C_JR, C_JALR}) begin
    instr_str = $sformatf("x%0d", this.get_addr_rd());
  end
  if (name inside {C_SLLI}) begin
    instr_str = $sformatf("x%0d, 0x%0x", this.get_addr_rd(), this.get_data_imm());
  end
  if (name inside {C_SRAI, C_SRLI}) begin
    instr_str = $sformatf("x%0d, 0x%0x", this.decode_rs1_c($signed(this.rvfi.insn)), this.get_data_imm());
  end
  if (name == C_ANDI) begin
    instr_str = $sformatf("x%0d, %0d", this.decode_rs1_c($signed(this.rvfi.insn)), $signed(this.get_data_imm()));
  end
  if (name == FENCE) begin
    instr_str = "iorw, iorw";  // Note: If later found necessary, add support for `fence` arguments other than "iorw"
  end

  // Default printing of just the instruction name
  begin
    instr_name_t  nm = (name == C_NOP) ? C_ADDI : name;
    instr_str = $sformatf ("0x%08x\t%s %s", rvfi.pc_rdata, nm.name().tolower(), instr_str);
  end

  if (trap)
    instr_str = { instr_str, " TRAP" };
  if (illegal)
    instr_str = { instr_str, " ILLEGAL" };

  if (instr_str.getc(instr_str.len() - 1) == " ")
    instr_str = instr_str.substr(0, (instr_str.len() - 2));

  return instr_str;

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
    rs1_valid = 1;
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


function instr_value_t uvma_isacov_instr_c::get_instr_value_type(bit[XLEN-1:0] value, int unsigned width, bit is_signed);
  if (value == 0)
    return ZERO;

  if (is_signed)
    return value[width-1] ? NEGATIVE : POSITIVE;

  return NON_ZERO;

endfunction : get_instr_value_type


function  int  uvma_isacov_instr_c::get_field_imm();

  bit [63:0] instr = $signed(this.rvfi.insn);

  // TODO:ropeders implement for 32-bit formats too, or add "c_" to the name

  // Return imm based on specific instruction first
  if (this.name == C_ADDI16SP) begin
    return dasm_rvc_addi16sp_imm(instr) >> 4;  // Shift 4 because [9:4] to [5:0]
  end

  // Return imm based on type
  if (this.itype == CI_TYPE) begin
    return dasm_rvc_imm(instr);
  end
  if (this.itype == CSS_TYPE) begin
    return (dasm_rvc_swsp_imm(instr) >> 2);  // Shift 2 because [7:2] to [5:0]
  end
  if (this.itype == CIW_TYPE) begin
    return (dasm_rvc_addi4spn_imm(instr) >> 2);  // Shift 2 because [9:2] to [7:0]
  end
  if (this.itype inside {CL_TYPE, CS_TYPE}) begin
    return (dasm_rvc_lw_imm(instr) >> 2);  // Shift 2 because [6:2] to [4:0]
  end
  if (this.itype == CB_TYPE) begin
    // TODO:ropeders make up new format names to differentiate? CB_TYPE_A, CB_TYPE_B?
    if (this.name inside {C_BEQZ, C_BNEZ}) begin
      return (dasm_rvc_b_imm(instr) >> 1);  // Shift 1 because [8:1] to [7:0]
    end else begin
      return dasm_rvc_imm(instr);
    end
  end
  if (this.itype == CJ_TYPE) begin
    return (dasm_rvc_j_imm(instr) >> 1);  // Shift 1 because [11:1] to [10:0]
  end

  // Note: 64-bit and 128-bit might require refinement of the above filtering

  return 0;

endfunction : get_field_imm


function  int  uvma_isacov_instr_c::get_field_rs1();

  return (itype inside {CL_TYPE, CS_TYPE, CA_TYPE, CB_TYPE}) ? rs1[2:0] : rs1;

endfunction : get_field_rs1


function  int  uvma_isacov_instr_c::get_field_rs2();

  return (itype inside {CS_TYPE, CA_TYPE}) ? rs2[2:0] : rs2;

endfunction : get_field_rs2


function  int  uvma_isacov_instr_c::get_field_rd();

  // TODO:ropeders is CA handled properly?
  // TODO:ropeders call dpi_dasm from here, instead of elsewhere?

  return (itype inside {CA_TYPE, CL_TYPE, CIW_TYPE, CB_TYPE}) ? rd[2:0] : rd;

endfunction : get_field_rd


function  int  uvma_isacov_instr_c::get_addr_rs1();

  bit [63:0] instr = $signed(this.rvfi.insn);
  int        rs1   = this.get_field_rs1();

  if (this.itype inside {CL_TYPE, CS_TYPE, CA_TYPE, CB_TYPE}) begin
    return rs1 + 8;
  end else begin
    return rs1;
  end

endfunction : get_addr_rs1


function  int  uvma_isacov_instr_c::get_addr_rs2();

  bit [63:0] instr = $signed(this.rvfi.insn);
  int        rs2   = this.get_field_rs2();

  if (this.itype inside {CS_TYPE, CA_TYPE}) begin
    return rs2 + 8;
  end else begin
    return rs2;
  end

endfunction : get_addr_rs2


function  int  uvma_isacov_instr_c::get_addr_rd();

  bit [63:0] instr = $signed(this.rvfi.insn);
  int        rd    = this.get_field_rd();

  if (this.itype inside {CIW_TYPE, CL_TYPE, CA_TYPE, CB_TYPE}) begin
    return rd + 8;
  end else begin
    return rd;
  end

endfunction : get_addr_rd


function  int  uvma_isacov_instr_c::get_data_imm();

  bit [63:0] instr = $signed(this.rvfi.insn);
  int        imm   = this.get_field_imm();

  if (this.itype inside {CSS_TYPE, CIW_TYPE, CS_TYPE, CL_TYPE}) begin
    return {imm, 2'b 00};
  end
  if (this.itype inside {CJ_TYPE} || this.name inside {C_BEQZ, C_BNEZ}) begin
    return {imm, 1'b 0};
  end
  if (this.name inside {C_ADDI16SP}) begin
    return {imm, 4'b 0000};
  end
  if (this.name inside {C_LUI}) begin
    return imm[19:0];  // TODO:ropeders should adhere to "LUI-semantics" or "RVC-semantics"?
  end

  return imm;

endfunction : get_data_imm

function int uvma_isacov_instr_c::decode_rd_c(bit[ILEN-1:0] instr); //function to extract the rd' (3 bits) address from a compressed instruction

  return instr[4:2] + 8;

endfunction : decode_rd_c

function int uvma_isacov_instr_c::decode_rs1_c(bit[ILEN-1:0] instr); //function to extract the rs1' (3 bits) address from a compressed instruction

  return instr[9:7] + 8;

endfunction : decode_rs1_c

function int uvma_isacov_instr_c::decode_rs2_c(bit[ILEN-1:0] instr); //function to extract the rs2' (3 bits) address from a compressed instruction

  return instr[4:2] + 8;

endfunction : decode_rs2_c

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

