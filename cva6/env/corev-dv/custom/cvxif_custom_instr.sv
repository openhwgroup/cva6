// Copyright 2022 Thales DIS design services SAS
// Copyright 2022 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)
// ------------------------------------------------------------------------------ //

`ifndef __CVXIF_CUSTOM_INSTR_SV__
`define __CVXIF_CUSTOM_INSTR_SV__

/**
 * This class describe custom instructions used with the cvxif agent.
 */
class cvxif_custom_instr extends riscv_custom_instr;

   rand riscv_reg_t rs1;
   rand riscv_reg_t rs2;
   rand riscv_reg_t rs3;

   `uvm_object_utils(cvxif_custom_instr)
   `uvm_object_new

   virtual function string get_instr_name();
      get_instr_name = instr_name.name();
      return get_instr_name;
   endfunction : get_instr_name

   // Convert the instruction to assembly code
   virtual function string convert2asm(string prefix = "");
      string asm_str;
      asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
      case (instr_name)
         CUS_ADD:       asm_str = $sformatf("%0s %0s, %0s, %0s",      asm_str, rd.name(),  rs1.name(),  rs2.name());
         CUS_ADD_MULTI: asm_str = $sformatf("%0s %0s, %0s, %0s",      asm_str, rd.name(),  rs1.name(),  rs2.name());
         CUS_ADD_RS3:   asm_str = $sformatf("%0s %0s, %0s, %0s, %0s", asm_str, rd.name(),  rs1.name(),  rs2.name(), rs3.name());
         CUS_NOP:       asm_str = "cus_nop";
         /* following instructions are not yet supported by cva6 */
         //CUS_EXC:       asm_str = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(),  rs1.name(),  rs2.name());
         //CUS_M_ADD:     asm_str = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(),  rs1.name(),  rs2.name());
         //CUS_S_ADD:     asm_str = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(),  rs1.name(),  rs2.name());
         //CUS_NOP_EXC:   asm_str = "cus_nop_exc";
         //CUS_ISS_EXC:   asm_str = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(),  rs1.name(),  rs2.name());
      endcase
      comment = {get_instr_name(), " ", comment};
      if (comment != "") begin
         asm_str = {asm_str, " #", comment};
      end
      return asm_str.tolower();
   endfunction : convert2asm

   virtual function void set_imm_len();
      imm_len = 7;
   endfunction : set_imm_len

   function bit [6:0] get_opcode();
      case (instr_name) inside
         {CUS_ADD, CUS_ADD_MULTI, CUS_ADD_RS3, CUS_NOP}        : get_opcode = 7'b1111011;
         // {CUS_ADD, CUS_ADD_MULTI, CUS_ADD_RS3, CUS_NOP, CUS_EXC, , CUS_NOP_EXC, CUS_ISS_EXC, CUS_M_ADD, CUS_S_ADD}   : get_opcode = 7'b1111011;
         default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
      endcase
   endfunction

   virtual function bit [2:0] get_func3();
      case (instr_name) inside
         {CUS_ADD, CUS_ADD_MULTI, CUS_ADD_RS3, CUS_NOP}        : get_func3 = 3'b000;
         // {CUS_ADD, CUS_ADD_MULTI, CUS_ADD_RS3, CUS_NOP, CUS_EXC, CUS_NOP_EXC, CUS_ISS_EXC, CUS_M_ADD, CUS_S_ADD} : get_func3 = 3'b000;
      endcase
   endfunction

   virtual function bit [6:0] get_func7();
      case (instr_name)
         CUS_ADD                    : get_func7 = 7'b0000000;
         CUS_NOP                    : get_func7 = 7'b0000000;
         CUS_ADD_MULTI              : get_func7 = 7'b0001000;
         // CUS_EXC                 : get_func7 = 7'b1000000;
         // CUS_M_ADD               : get_func7 = 7'b0000010;
         // CUS_S_ADD               : get_func7 = 7'b0000110;
         // CUS_NOP_EXC             : get_func7 = 7'b0100000;
         // CUS_ISS_EXC             : get_func7 = 7'b1100000;
      endcase
   endfunction

   virtual function bit [6:0] get_func2();
      case (instr_name)
         CUS_ADD_RS3                : get_func2 = 2'b01;
      endcase
   endfunction

   virtual function void set_rand_mode();
      /*case (instr_name) inside
         "CUS_EXC", "CUS_ISS_EXC": begin
            has_rd= 1'b0;
            has_rs2= 1'b0;
         end
      endcase*/
  endfunction

   function void pre_randomize();
      rd.rand_mode(has_rd);
      rs2.rand_mode(has_rs2);
   endfunction

   constraint rd_c {
      // if (instr_name inside {CUS_ADD_MULTI, CUS_ADD, CUS_ADD_RS3, CUS_M_ADD, CUS_S_ADD}) {
      if (instr_name inside {CUS_ADD_MULTI, CUS_ADD, CUS_ADD_RS3}) {
         rd!=0;
      }
  /* if (instr_name inside { CUS_EXC, CUS_ISS_EXC} ) {
      rd == 0;
      rs1 inside {[4:7], 13, 15};
      rs2 == 0;
    }*/
  }

endclass

`endif // __CVXIF_CUSTOM_INSTR_SV__
