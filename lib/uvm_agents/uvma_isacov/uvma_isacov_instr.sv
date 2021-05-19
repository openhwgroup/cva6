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
  instr_type_t  itype;
  instr_group_t group;

  instr_csr_t   csr;

  bit [4:0] rs1;
  bit [4:0] rs2;
  bit [4:0] rd;
  bit [11:0] immi;
  bit [11:0] imms;
  bit [12:1] immb;
  bit [19:0] immu;
  bit [20:1] immj;

  // Valid flags for fields (to calculate hazards and other coverage)
  bit rs1_valid;
  bit rs2_valid;
  bit rd_valid;

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
    `uvm_field_enum(instr_type_t, itype, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_group_t, group, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_enum(instr_csr_t, csr, UVM_ALL_ON | UVM_NOPRINT);

    `uvm_field_int(rs1_valid, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs1_valid, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs2_valid, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rs2_valid, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rd_valid, UVM_ALL_ON | UVM_NOPRINT);
    `uvm_field_int(rd_valid, UVM_ALL_ON | UVM_NOPRINT);

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

  extern function void set_valid_flags();
  extern function bit is_csr_write();
endclass : uvma_isacov_instr_c

function uvma_isacov_instr_c::new(string name = "isacov_instr");
  super.new(name);
endfunction : new

function string uvma_isacov_instr_c::convert2string();

  if (itype == R_TYPE) begin
    return $sformatf("%s x%0d, x%0d, x%0d", name.name(), rd, rs1, rs2);
  end
  if (itype == I_TYPE) begin
    return $sformatf("%s x%0d, x%0d, %0d", name.name(), rd, rs1, immi);
  end
  if (itype == S_TYPE) begin
    return $sformatf("%s x%0d, %0d(x%0d)", name.name(), rs2, imms, rs1);
  end
  if (itype == B_TYPE) begin
    return $sformatf("%s x%0d, x%0d, %0d)", name.name(), rs1, rs1, immb);
  end
  if (itype == U_TYPE) begin
    return $sformatf("%s x%0d, %0d", name.name(), rd, immu);
  end
  if (itype == J_TYPE) begin
    return $sformatf("%s x%0d, %0d", name.name(), rd, immj);
  end
  if (itype == CSR_TYPE) begin
    return $sformatf("%s x%0d, x%0d, %0d", name.name(), rd, rs1, immi);
  end

  return name.name();
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
  end

  if (itype == S_TYPE) begin
    rs1_valid = 1;
    rs2_valid = 1;    
  end

  if (itype == B_TYPE) begin
    rs1_valid = 1;
    rs2_valid = 1;    
  end

  if (itype == U_TYPE) begin
    rd_valid = 1;
  end

  if (itype == J_TYPE) begin
    rd_valid = 1;
  end

  if (itype == CSR_TYPE) begin
    rs1_valid = 1;
    rd_valid = 1;
  end

  if (itype == CSRI_TYPE) begin
    rd_valid = 1;
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
