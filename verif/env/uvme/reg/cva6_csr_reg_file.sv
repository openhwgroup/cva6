//
// Copyright 2020 OpenHW Group
// Copyright 2023 Thales DIS
//
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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

typedef enum int {
   U_LEVEL        = 0,
   S_LEVEL        = 1,
   RESERVED_LEVEL = 2,
   M_LEVEL        = 3,
   D_LEVEL        = 10
} privilege_level_t;
 
class csr_reg extends uvm_reg;

  local privilege_level_t privilege_level; //CSR Privilege access level 
  
  `uvm_object_utils_begin(csr_reg)
      `uvm_field_enum(privilege_level_t, privilege_level, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "csr_reg");
    super.new(name, .n_bits(32), .has_coverage(UVM_CVR_ALL));
  endfunction
  
  function  int get_privilege_level(); 
      return privilege_level;
  endfunction

  function  string get_privilege_level_str(privilege_level_t privilege); 
   case (privilege)
      U_LEVEL: return "U";
      S_LEVEL: return "S";
      M_LEVEL: return "M";
      D_LEVEL: return "D";
   endcase
   return "?";
  endfunction

  function void set_privilege_level(privilege_level_t privilege); 
      privilege_level = privilege;
  endfunction

  virtual function void sample(uvm_reg_data_t data, uvm_reg_data_t byte_en,bit is_read, uvm_reg_map map);
     sample_values();
  endfunction

endclass

class reg_mstatus extends csr_reg;
  `uvm_object_utils(reg_mstatus)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field SD;
  rand uvm_reg_field TSR;
  rand uvm_reg_field TW;
  rand uvm_reg_field TVM;
  rand uvm_reg_field MXR;
  rand uvm_reg_field SUM;
  rand uvm_reg_field MPRV;
  rand uvm_reg_field XS;
  rand uvm_reg_field FS;
  rand uvm_reg_field MPP;
  rand uvm_reg_field VS;
  rand uvm_reg_field SPP;
  rand uvm_reg_field MPIE;
  rand uvm_reg_field UBE;
  rand uvm_reg_field SPIE;
  rand uvm_reg_field MIE;
  rand uvm_reg_field SIE;
   

  covergroup cg_vals;
      option.name = "csr_mstatus";
      option.per_instance = 1;
      SD: coverpoint SD.value[0:0];
      TSR: coverpoint TSR.value[0:0];
      TW: coverpoint TW.value[0:0];
      TVM: coverpoint TVM.value[0:0];
      MXR: coverpoint MXR.value[0:0];
      SUM: coverpoint SUM.value[0:0];
      MPRV: coverpoint MPRV.value[0:0];
      XS: coverpoint XS.value[1:0];
      FS: coverpoint FS.value[1:0];
      MPP: coverpoint MPP.value[1:0];
      VS: coverpoint VS.value[1:0];
      SPP: coverpoint SPP.value[0:0];
      MPIE: coverpoint MPIE.value[0:0];
      UBE: coverpoint UBE.value[0:0];
      SPIE: coverpoint SPIE.value[0:0];
      MIE: coverpoint MIE.value[0:0];
      SIE: coverpoint SIE.value[0:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mstatus");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mstatus");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    SD = uvm_reg_field::type_id::create("SD");   
    SD.configure(.parent(this), .size(1), .lsb_pos(31), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    TSR = uvm_reg_field::type_id::create("TSR");   
    TSR.configure(.parent(this), .size(1), .lsb_pos(22), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    TW = uvm_reg_field::type_id::create("TW");   
    TW.configure(.parent(this), .size(1), .lsb_pos(21), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    TVM = uvm_reg_field::type_id::create("TVM");   
    TVM.configure(.parent(this), .size(1), .lsb_pos(20), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MXR = uvm_reg_field::type_id::create("MXR");   
    MXR.configure(.parent(this), .size(1), .lsb_pos(19), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    SUM = uvm_reg_field::type_id::create("SUM");   
    SUM.configure(.parent(this), .size(1), .lsb_pos(18), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MPRV = uvm_reg_field::type_id::create("MPRV");   
    MPRV.configure(.parent(this), .size(1), .lsb_pos(17), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    XS = uvm_reg_field::type_id::create("XS");   
    XS.configure(.parent(this), .size(2), .lsb_pos(15), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    FS = uvm_reg_field::type_id::create("FS");   
    FS.configure(.parent(this), .size(2), .lsb_pos(13), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MPP = uvm_reg_field::type_id::create("MPP");   
    MPP.configure(.parent(this), .size(2), .lsb_pos(11), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    VS = uvm_reg_field::type_id::create("VS");   
    VS.configure(.parent(this), .size(2), .lsb_pos(9), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    SPP = uvm_reg_field::type_id::create("SPP");   
    SPP.configure(.parent(this), .size(1), .lsb_pos(8), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MPIE = uvm_reg_field::type_id::create("MPIE");   
    MPIE.configure(.parent(this), .size(1), .lsb_pos(7), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    UBE = uvm_reg_field::type_id::create("UBE");   
    UBE.configure(.parent(this), .size(1), .lsb_pos(6), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    SPIE = uvm_reg_field::type_id::create("SPIE");   
    SPIE.configure(.parent(this), .size(1), .lsb_pos(5), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    MIE = uvm_reg_field::type_id::create("MIE");   
    MIE.configure(.parent(this), .size(1), .lsb_pos(3), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    SIE = uvm_reg_field::type_id::create("SIE");   
    SIE.configure(.parent(this), .size(1), .lsb_pos(1), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_misa extends csr_reg;
  `uvm_object_utils(reg_misa)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field MXL;
  rand uvm_reg_field Extensions;
   

  covergroup cg_vals;
      option.name = "csr_misa";
      option.per_instance = 1;
      MXL: coverpoint MXL.value[1:0];
      Extensions: coverpoint Extensions.value[25:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_misa");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.misa");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    MXL = uvm_reg_field::type_id::create("MXL");   
    MXL.configure(.parent(this), .size(2), .lsb_pos(30), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    Extensions = uvm_reg_field::type_id::create("Extensions");   
    Extensions.configure(.parent(this), .size(26), .lsb_pos(0), .access("RW"), .volatile(0), .reset(37782532), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mie extends csr_reg;
  `uvm_object_utils(reg_mie)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field MEIE;
  rand uvm_reg_field SEIE;
  rand uvm_reg_field UEIE;
  rand uvm_reg_field MTIE;
  rand uvm_reg_field STIE;
  rand uvm_reg_field UTIE;
  rand uvm_reg_field MSIE;
  rand uvm_reg_field SSIE;
  rand uvm_reg_field USIE;
   

  covergroup cg_vals;
      option.name = "csr_mie";
      option.per_instance = 1;
      MEIE: coverpoint MEIE.value[0:0];
      SEIE: coverpoint SEIE.value[0:0];
      UEIE: coverpoint UEIE.value[0:0];
      MTIE: coverpoint MTIE.value[0:0];
      STIE: coverpoint STIE.value[0:0];
      UTIE: coverpoint UTIE.value[0:0];
      MSIE: coverpoint MSIE.value[0:0];
      SSIE: coverpoint SSIE.value[0:0];
      USIE: coverpoint USIE.value[0:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mie");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mie");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
   
    MEIE = uvm_reg_field::type_id::create("MEIE");   
    MEIE.configure(.parent(this), .size(1), .lsb_pos(11), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    SEIE = uvm_reg_field::type_id::create("SEIE");   
    SEIE.configure(.parent(this), .size(1), .lsb_pos(9), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    UEIE = uvm_reg_field::type_id::create("UEIE");   
    UEIE.configure(.parent(this), .size(1), .lsb_pos(8), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MTIE = uvm_reg_field::type_id::create("MTIE");   
    MTIE.configure(.parent(this), .size(1), .lsb_pos(7), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    STIE = uvm_reg_field::type_id::create("STIE");   
    STIE.configure(.parent(this), .size(1), .lsb_pos(5), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    UTIE = uvm_reg_field::type_id::create("UTIE");   
    UTIE.configure(.parent(this), .size(1), .lsb_pos(4), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MSIE = uvm_reg_field::type_id::create("MSIE");   
    MSIE.configure(.parent(this), .size(1), .lsb_pos(3), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    SSIE = uvm_reg_field::type_id::create("SSIE");   
    SSIE.configure(.parent(this), .size(1), .lsb_pos(1), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    USIE = uvm_reg_field::type_id::create("USIE");   
    USIE.configure(.parent(this), .size(1), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mtvec extends csr_reg;
  `uvm_object_utils(reg_mtvec)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field BASE;
  rand uvm_reg_field MODE;
   

  covergroup cg_vals;
      option.name = "csr_mtvec";
      option.per_instance = 1;
      BASE: coverpoint BASE.value[29:0];
      MODE: coverpoint MODE.value[1:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mtvec");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mtvec");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    BASE = uvm_reg_field::type_id::create("BASE");   
    BASE.configure(.parent(this), .size(30), .lsb_pos(2), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MODE = uvm_reg_field::type_id::create("MODE");   
    MODE.configure(.parent(this), .size(2), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mstatush extends csr_reg;
  `uvm_object_utils(reg_mstatush)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field SBE;
  rand uvm_reg_field MBE;
   

  covergroup cg_vals;
      option.name = "csr_mstatush";
      option.per_instance = 1;
      SBE: coverpoint SBE.value[0:0];
      MBE: coverpoint MBE.value[0:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mstatush");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mstatush");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
   
    SBE = uvm_reg_field::type_id::create("SBE");   
    SBE.configure(.parent(this), .size(1), .lsb_pos(4), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MBE = uvm_reg_field::type_id::create("MBE");   
    MBE.configure(.parent(this), .size(1), .lsb_pos(5), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent3 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent3)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent3";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent3");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent3");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent4 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent4)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent4";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent4");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent4");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent5 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent5)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent5";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent5");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent5");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent6 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent6)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent6";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent6");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent6");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent7 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent7)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent7";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent7");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent7");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent8 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent8)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent8";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent8");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent8");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent9 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent9)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent9";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent9");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent9");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent10 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent10)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent10";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent10");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent10");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent11 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent11)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent11";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent11");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent11");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent12 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent12)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent12";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent12");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent12");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent13 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent13)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent13";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent13");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent13");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent14 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent14)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent14";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent14");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent14");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent15 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent15)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent15";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent15");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent15");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent16 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent16)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent16";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent16");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent16");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent17 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent17)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent17";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent17");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent17");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent18 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent18)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent18";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent18");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent18");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent19 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent19)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent19";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent19");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent19");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent20 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent20)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent20";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent20");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent20");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent21 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent21)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent21";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent21");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent21");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent22 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent22)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent22";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent22");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent22");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent23 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent23)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent23";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent23");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent23");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent24 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent24)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent24";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent24");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent24");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent25 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent25)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent25";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent25");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent25");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent26 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent26)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent26";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent26");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent26");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent27 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent27)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent27";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent27");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent27");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent28 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent28)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent28";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent28");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent28");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent29 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent29)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent29";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent29");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent29");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent30 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent30)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent30";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent30");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent30");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmevent31 extends csr_reg;
  `uvm_object_utils(reg_mhpmevent31)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mhpmevent;
   

  covergroup cg_vals;
      option.name = "csr_mhpmevent31";
      option.per_instance = 1;
      mhpmevent: coverpoint mhpmevent.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmevent31");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmevent31");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mhpmevent = uvm_reg_field::type_id::create("mhpmevent");   
    mhpmevent.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mscratch extends csr_reg;
  `uvm_object_utils(reg_mscratch)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mscratch;
   

  covergroup cg_vals;
      option.name = "csr_mscratch";
      option.per_instance = 1;
      mscratch: coverpoint mscratch.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mscratch");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mscratch");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mscratch = uvm_reg_field::type_id::create("mscratch");   
    mscratch.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mepc extends csr_reg;
  `uvm_object_utils(reg_mepc)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mepc;
   

  covergroup cg_vals;
      option.name = "csr_mepc";
      option.per_instance = 1;
      mepc: coverpoint mepc.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mepc");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mepc");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mepc = uvm_reg_field::type_id::create("mepc");   
    mepc.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mcause extends csr_reg;
  `uvm_object_utils(reg_mcause)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field Interrupt;
  rand uvm_reg_field exception_code;
   

  covergroup cg_vals;
      option.name = "csr_mcause";
      option.per_instance = 1;
      Interrupt: coverpoint Interrupt.value[0:0];
      exception_code: coverpoint exception_code.value[30:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mcause");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mcause");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    Interrupt = uvm_reg_field::type_id::create("Interrupt");   
    Interrupt.configure(.parent(this), .size(1), .lsb_pos(31), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    exception_code = uvm_reg_field::type_id::create("exception_code");   
    exception_code.configure(.parent(this), .size(31), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mtval extends csr_reg;
  `uvm_object_utils(reg_mtval)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field mtval;
   

  covergroup cg_vals;
      option.name = "csr_mtval";
      option.per_instance = 1;
      mtval: coverpoint mtval.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mtval");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mtval");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    mtval = uvm_reg_field::type_id::create("mtval");   
    mtval.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mip extends csr_reg;
  `uvm_object_utils(reg_mip)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field MEIP;
  rand uvm_reg_field SEIP;
  rand uvm_reg_field UEIP;
  rand uvm_reg_field MTIP;
  rand uvm_reg_field STIP;
  rand uvm_reg_field UTIP;
  rand uvm_reg_field MSIP;
  rand uvm_reg_field SSIP;
  rand uvm_reg_field USIP;
   

  covergroup cg_vals;
      option.name = "csr_mip";
      option.per_instance = 1;
      MEIP: coverpoint MEIP.value[0:0];
      SEIP: coverpoint SEIP.value[0:0];
      UEIP: coverpoint UEIP.value[0:0];
      MTIP: coverpoint MTIP.value[0:0];
      STIP: coverpoint STIP.value[0:0];
      UTIP: coverpoint UTIP.value[0:0];
      MSIP: coverpoint MSIP.value[0:0];
      SSIP: coverpoint SSIP.value[0:0];
      USIP: coverpoint USIP.value[0:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mip");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mip");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
   
    MEIP = uvm_reg_field::type_id::create("MEIP");   
    MEIP.configure(.parent(this), .size(1), .lsb_pos(11), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    SEIP = uvm_reg_field::type_id::create("SEIP");   
    SEIP.configure(.parent(this), .size(1), .lsb_pos(9), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    UEIP = uvm_reg_field::type_id::create("UEIP");   
    UEIP.configure(.parent(this), .size(1), .lsb_pos(8), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MTIP = uvm_reg_field::type_id::create("MTIP");   
    MTIP.configure(.parent(this), .size(1), .lsb_pos(7), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    STIP = uvm_reg_field::type_id::create("STIP");   
    STIP.configure(.parent(this), .size(1), .lsb_pos(5), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    UTIP = uvm_reg_field::type_id::create("UTIP");   
    UTIP.configure(.parent(this), .size(1), .lsb_pos(4), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    MSIP = uvm_reg_field::type_id::create("MSIP");   
    MSIP.configure(.parent(this), .size(1), .lsb_pos(3), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
   
    SSIP = uvm_reg_field::type_id::create("SSIP");   
    SSIP.configure(.parent(this), .size(1), .lsb_pos(1), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    USIP = uvm_reg_field::type_id::create("USIP");   
    USIP.configure(.parent(this), .size(1), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpcfg0 extends csr_reg;
  `uvm_object_utils(reg_pmpcfg0)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field pmp3cfg;
  rand uvm_reg_field pmp2cfg;
  rand uvm_reg_field pmp1cfg;
  rand uvm_reg_field pmp0cfg;
   

  covergroup cg_vals;
      option.name = "csr_pmpcfg0";
      option.per_instance = 1;
      pmp3cfg: coverpoint pmp3cfg.value[7:0];
      pmp2cfg: coverpoint pmp2cfg.value[7:0];
      pmp1cfg: coverpoint pmp1cfg.value[7:0];
      pmp0cfg: coverpoint pmp0cfg.value[7:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpcfg0");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpcfg0");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    pmp3cfg = uvm_reg_field::type_id::create("pmp3cfg");   
    pmp3cfg.configure(.parent(this), .size(8), .lsb_pos(24), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp2cfg = uvm_reg_field::type_id::create("pmp2cfg");   
    pmp2cfg.configure(.parent(this), .size(8), .lsb_pos(16), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp1cfg = uvm_reg_field::type_id::create("pmp1cfg");   
    pmp1cfg.configure(.parent(this), .size(8), .lsb_pos(8), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp0cfg = uvm_reg_field::type_id::create("pmp0cfg");   
    pmp0cfg.configure(.parent(this), .size(8), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpcfg1 extends csr_reg;
  `uvm_object_utils(reg_pmpcfg1)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field pmp7cfg;
  rand uvm_reg_field pmp6cfg;
  rand uvm_reg_field pmp5cfg;
  rand uvm_reg_field pmp4cfg;
   

  covergroup cg_vals;
      option.name = "csr_pmpcfg1";
      option.per_instance = 1;
      pmp7cfg: coverpoint pmp7cfg.value[7:0];
      pmp6cfg: coverpoint pmp6cfg.value[7:0];
      pmp5cfg: coverpoint pmp5cfg.value[7:0];
      pmp4cfg: coverpoint pmp4cfg.value[7:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpcfg1");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpcfg1");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    pmp7cfg = uvm_reg_field::type_id::create("pmp7cfg");   
    pmp7cfg.configure(.parent(this), .size(8), .lsb_pos(24), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp6cfg = uvm_reg_field::type_id::create("pmp6cfg");   
    pmp6cfg.configure(.parent(this), .size(8), .lsb_pos(16), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp5cfg = uvm_reg_field::type_id::create("pmp5cfg");   
    pmp5cfg.configure(.parent(this), .size(8), .lsb_pos(8), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp4cfg = uvm_reg_field::type_id::create("pmp4cfg");   
    pmp4cfg.configure(.parent(this), .size(8), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpcfg2 extends csr_reg;
  `uvm_object_utils(reg_pmpcfg2)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field pmp11cfg;
  rand uvm_reg_field pmp10cfg;
  rand uvm_reg_field pmp9cfg;
  rand uvm_reg_field pmp8cfg;
   

  covergroup cg_vals;
      option.name = "csr_pmpcfg2";
      option.per_instance = 1;
      pmp11cfg: coverpoint pmp11cfg.value[7:0];
      pmp10cfg: coverpoint pmp10cfg.value[7:0];
      pmp9cfg: coverpoint pmp9cfg.value[7:0];
      pmp8cfg: coverpoint pmp8cfg.value[7:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpcfg2");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpcfg2");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    pmp11cfg = uvm_reg_field::type_id::create("pmp11cfg");   
    pmp11cfg.configure(.parent(this), .size(8), .lsb_pos(24), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp10cfg = uvm_reg_field::type_id::create("pmp10cfg");   
    pmp10cfg.configure(.parent(this), .size(8), .lsb_pos(16), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp9cfg = uvm_reg_field::type_id::create("pmp9cfg");   
    pmp9cfg.configure(.parent(this), .size(8), .lsb_pos(8), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp8cfg = uvm_reg_field::type_id::create("pmp8cfg");   
    pmp8cfg.configure(.parent(this), .size(8), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpcfg3 extends csr_reg;
  `uvm_object_utils(reg_pmpcfg3)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field pmp15cfg;
  rand uvm_reg_field pmp14cfg;
  rand uvm_reg_field pmp13cfg;
  rand uvm_reg_field pmp12cfg;
   

  covergroup cg_vals;
      option.name = "csr_pmpcfg3";
      option.per_instance = 1;
      pmp15cfg: coverpoint pmp15cfg.value[7:0];
      pmp14cfg: coverpoint pmp14cfg.value[7:0];
      pmp13cfg: coverpoint pmp13cfg.value[7:0];
      pmp12cfg: coverpoint pmp12cfg.value[7:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpcfg3");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpcfg3");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    pmp15cfg = uvm_reg_field::type_id::create("pmp15cfg");   
    pmp15cfg.configure(.parent(this), .size(8), .lsb_pos(24), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp14cfg = uvm_reg_field::type_id::create("pmp14cfg");   
    pmp14cfg.configure(.parent(this), .size(8), .lsb_pos(16), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp13cfg = uvm_reg_field::type_id::create("pmp13cfg");   
    pmp13cfg.configure(.parent(this), .size(8), .lsb_pos(8), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    pmp12cfg = uvm_reg_field::type_id::create("pmp12cfg");   
    pmp12cfg.configure(.parent(this), .size(8), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr0 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr0)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr0";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr0");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr0");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr1 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr1)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr1";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr1");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr1");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr2 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr2)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr2";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr2");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr2");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr3 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr3)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr3";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr3");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr3");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr4 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr4)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr4";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr4");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr4");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr5 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr5)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr5";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr5");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr5");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr6 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr6)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr6";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr6");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr6");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr7 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr7)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr7";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr7");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr7");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr8 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr8)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr8";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr8");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr8");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr9 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr9)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr9";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr9");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr9");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr10 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr10)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr10";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr10");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr10");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr11 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr11)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr11";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr11");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr11");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr12 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr12)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr12";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr12");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr12");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr13 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr13)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr13";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr13");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr13");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr14 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr14)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr14";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr14");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr14");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_pmpaddr15 extends csr_reg;
  `uvm_object_utils(reg_pmpaddr15)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field address;
   

  covergroup cg_vals;
      option.name = "csr_pmpaddr15";
      option.per_instance = 1;
      address: coverpoint address.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_pmpaddr15");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.pmpaddr15");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    address = uvm_reg_field::type_id::create("address");   
    address.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_icache extends csr_reg;
  `uvm_object_utils(reg_icache)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field icache;
   

  covergroup cg_vals;
      option.name = "csr_icache";
      option.per_instance = 1;
      icache: coverpoint icache.value[0:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_icache");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.icache");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
   
    icache = uvm_reg_field::type_id::create("icache");   
    icache.configure(.parent(this), .size(1), .lsb_pos(0), .access("RW"), .volatile(0), .reset(1), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mcycle extends csr_reg;
  `uvm_object_utils(reg_mcycle)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mcycle";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mcycle");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mcycle");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_minstret extends csr_reg;
  `uvm_object_utils(reg_minstret)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_minstret";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_minstret");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.minstret");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mcycleh extends csr_reg;
  `uvm_object_utils(reg_mcycleh)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mcycleh";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mcycleh");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mcycleh");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_minstreth extends csr_reg;
  `uvm_object_utils(reg_minstreth)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_minstreth";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_minstreth");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.minstreth");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter3 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter3)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter3";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter3");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter3");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter4 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter4)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter4";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter4");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter4");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter5 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter5)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter5";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter5");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter5");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter6 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter6)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter6";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter6");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter6");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter7 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter7)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter7";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter7");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter7");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter8 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter8)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter8";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter8");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter8");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter9 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter9)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter9";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter9");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter9");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter10 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter10)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter10";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter10");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter10");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter11 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter11)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter11";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter11");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter11");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter12 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter12)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter12";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter12");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter12");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter13 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter13)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter13";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter13");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter13");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter14 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter14)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter14";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter14");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter14");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter15 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter15)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter15";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter15");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter15");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter16 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter16)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter16";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter16");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter16");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter17 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter17)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter17";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter17");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter17");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter18 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter18)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter18";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter18");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter18");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter19 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter19)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter19";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter19");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter19");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter20 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter20)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter20";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter20");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter20");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter21 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter21)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter21";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter21");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter21");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter22 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter22)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter22";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter22");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter22");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter23 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter23)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter23";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter23");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter23");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter24 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter24)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter24";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter24");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter24");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter25 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter25)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter25";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter25");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter25");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter26 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter26)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter26";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter26");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter26");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter27 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter27)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter27";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter27");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter27");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter28 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter28)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter28";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter28");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter28");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter29 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter29)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter29";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter29");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter29");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter30 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter30)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter30";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter30");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter30");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounter31 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounter31)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounter31";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounter31");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounter31");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh3 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh3)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh3";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh3");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh3");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh4 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh4)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh4";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh4");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh4");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh5 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh5)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh5";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh5");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh5");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh6 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh6)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh6";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh6");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh6");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh7 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh7)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh7";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh7");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh7");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh8 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh8)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh8";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh8");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh8");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh9 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh9)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh9";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh9");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh9");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh10 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh10)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh10";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh10");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh10");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh11 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh11)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh11";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh11");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh11");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh12 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh12)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh12";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh12");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh12");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh13 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh13)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh13";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh13");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh13");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh14 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh14)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh14";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh14");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh14");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh15 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh15)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh15";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh15");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh15");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh16 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh16)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh16";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh16");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh16");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh17 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh17)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh17";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh17");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh17");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh18 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh18)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh18";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh18");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh18");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh19 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh19)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh19";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh19");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh19");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh20 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh20)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh20";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh20");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh20");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh21 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh21)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh21";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh21");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh21");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh22 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh22)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh22";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh22");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh22");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh23 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh23)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh23";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh23");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh23");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh24 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh24)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh24";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh24");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh24");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh25 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh25)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh25";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh25");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh25");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh26 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh26)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh26";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh26");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh26");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh27 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh27)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh27";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh27");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh27");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh28 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh28)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh28";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh28");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh28");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh29 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh29)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh29";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh29");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh29");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh30 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh30)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh30";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh30");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh30");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhpmcounterh31 extends csr_reg;
  `uvm_object_utils(reg_mhpmcounterh31)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_mhpmcounterh31";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhpmcounterh31");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhpmcounterh31");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RW"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_cycle extends csr_reg;
  `uvm_object_utils(reg_cycle)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_cycle";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_cycle");
    super.new(name);
    set_privilege_level(U_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.cycle");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_instret extends csr_reg;
  `uvm_object_utils(reg_instret)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_instret";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_instret");
    super.new(name);
    set_privilege_level(U_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.instret");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_cycleh extends csr_reg;
  `uvm_object_utils(reg_cycleh)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_cycleh";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_cycleh");
    super.new(name);
    set_privilege_level(U_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.cycleh");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_instreth extends csr_reg;
  `uvm_object_utils(reg_instreth)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field count;
   

  covergroup cg_vals;
      option.name = "csr_instreth";
      option.per_instance = 1;
      count: coverpoint count.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_instreth");
    super.new(name);
    set_privilege_level(U_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.instreth");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    count = uvm_reg_field::type_id::create("count");   
    count.configure(.parent(this), .size(32), .lsb_pos(0), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mvendorid extends csr_reg;
  `uvm_object_utils(reg_mvendorid)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field bank;
  rand uvm_reg_field offset;
   

  covergroup cg_vals;
      option.name = "csr_mvendorid";
      option.per_instance = 1;
      bank: coverpoint bank.value[24:0];
      offset: coverpoint offset.value[6:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mvendorid");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mvendorid");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    bank = uvm_reg_field::type_id::create("bank");   
    bank.configure(.parent(this), .size(25), .lsb_pos(7), .access("RO"), .volatile(0), .reset(384), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
   
    offset = uvm_reg_field::type_id::create("offset");   
    offset.configure(.parent(this), .size(7), .lsb_pos(0), .access("RO"), .volatile(0), .reset(64), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_marchid extends csr_reg;
  `uvm_object_utils(reg_marchid)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field architecture_id;
   

  covergroup cg_vals;
      option.name = "csr_marchid";
      option.per_instance = 1;
      architecture_id: coverpoint architecture_id.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_marchid");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.marchid");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    architecture_id = uvm_reg_field::type_id::create("architecture_id");   
    architecture_id.configure(.parent(this), .size(32), .lsb_pos(0), .access("RO"), .volatile(0), .reset(3), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mimpid extends csr_reg;
  `uvm_object_utils(reg_mimpid)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field implementation;
   

  covergroup cg_vals;
      option.name = "csr_mimpid";
      option.per_instance = 1;
      implementation: coverpoint implementation.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mimpid");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mimpid");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    implementation = uvm_reg_field::type_id::create("implementation");   
    implementation.configure(.parent(this), .size(32), .lsb_pos(0), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass


class reg_mhartid extends csr_reg;
  `uvm_object_utils(reg_mhartid)

  //---------------------------------------
  // fields instance 
  //--------------------------------------- 
  rand uvm_reg_field hart_id;
   

  covergroup cg_vals;
      option.name = "csr_mhartid";
      option.per_instance = 1;
      hart_id: coverpoint hart_id.value[31:0];
  endgroup

  //---------------------------------------
  // Constructor 
  //---------------------------------------
  function new (string name = "reg_mhartid");
    super.new(name);
    set_privilege_level(M_LEVEL);
    cg_vals = new();
    cg_vals.set_inst_name("csr_reg_cov.mhartid");
  endfunction

  //---------------------------------------
  // build_phase - 
  // 1. Create the fields
  // 2. Configure the fields
  //---------------------------------------  
  function void build; 
   
    hart_id = uvm_reg_field::type_id::create("hart_id");   
    hart_id.configure(.parent(this), .size(32), .lsb_pos(0), .access("RO"), .volatile(0), .reset(0), .has_reset(1), .is_rand(1),  .individually_accessible(0));  
  endfunction

  virtual function void sample_values();
    if (get_coverage(UVM_CVR_FIELD_VALS))
      cg_vals.sample();
  endfunction

endclass
