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

   rand riscv_reg_t rs3;

   `uvm_object_utils(cvxif_custom_instr)
   `uvm_object_new

   virtual function string get_instr_name();
      get_instr_name = instr_name.name();
      return get_instr_name;
   endfunction : get_instr_name


   constraint cus_rx {
      if (instr_name inside {CUS_EXC}) {
         rs1 dist { [0:9] := 10, 10 := 2, [11:13] := 10, 14 := 2, 15 := 10, [16:23] := 2, [25:31] := 2 };
      }
   }

   // Convert the instruction to assembly code
   virtual function string convert2asm(string prefix = "");
      string asm_str;
      asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
      case (instr_name)
         CUS_ADD:       asm_str = $sformatf("%0s %0s, %0s, %0s",      asm_str, rd.name(),  rs1.name(),  rs2.name());
         CUS_ADD_MULTI: asm_str = $sformatf("%0s %0s, %0s, %0s",      asm_str, rd.name(),  rs1.name(),  rs2.name());
         CUS_ADD_RS3:   asm_str = $sformatf("%0s %0s, %0s, %0s, %0s", asm_str, rd.name(),  rs1.name(),  rs2.name(), rs3.name());
         CUS_NOP:       asm_str = "cus_nop";
         CUS_S_ADD:     asm_str = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(),  rs1.name(),  rs2.name());
         CUS_U_ADD:     asm_str = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(),  rs1.name(),  rs2.name());
         CUS_EXC:       asm_str = $sformatf("%0s %0s",      asm_str, rs1.name());
      endcase
      comment = {get_instr_name(), " ", comment};
      if (comment != "") begin
         asm_str = {asm_str, " #", comment};
      end
      return asm_str.tolower();
   endfunction : convert2asm

   virtual function void set_imm_len();
      imm_len = 6;
   endfunction : set_imm_len

   function bit [6:0] get_opcode();
      case (instr_name) inside
         {CUS_ADD, CUS_ADD_MULTI, CUS_ADD_RS3, CUS_NOP, CUS_U_ADD, CUS_S_ADD, CUS_EXC}   : get_opcode = 7'b1111011;
         default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
      endcase
   endfunction

   virtual function bit [2:0] get_func3();
      case (instr_name) inside
         CUS_ADD_MULTI, CUS_ADD_RS3, CUS_U_ADD, CUS_S_ADD        : get_func3 = 3'b000;
         CUS_ADD                                                 : get_func3 = 3'b001;
         CUS_EXC                                                 : get_func3 = 3'b010;
      endcase
   endfunction

   virtual function bit [6:0] get_func7();
      case (instr_name)
         CUS_ADD                    : get_func7 = 7'b0000000;
         CUS_NOP                    : get_func7 = 7'b0000000;
         CUS_ADD_MULTI              : get_func7 = 7'b0001000;
         CUS_U_ADD                  : get_func7 = 7'b0000010;
         CUS_S_ADD                  : get_func7 = 7'b0000110;
         CUS_EXC                    : get_func7 = 7'b1100000;
      endcase
   endfunction

   virtual function bit [1:0] get_func2();
      case (instr_name)
         CUS_ADD_RS3                : get_func2 = 2'b01;
      endcase
   endfunction

   virtual function void set_rand_mode();
      case (instr_name) inside
         "CUS_NOP": begin
            has_rd  = 1'b0;
            has_rs1 = 1'b0;
            has_rs2 = 1'b0;
            has_imm = 1'b0;
         end
         "CUS_EXC": begin
            has_rd  = 1'b0;
            has_rs1 = 1'b1;
            has_rs2 = 1'b0;
            has_imm = 1'b0;
         end
      endcase
   endfunction

   function void pre_randomize();
      rd.rand_mode(has_rd);
      rs1.rand_mode(has_rs1);
      rs2.rand_mode(has_rs2);
      imm.rand_mode(has_imm);
   endfunction

   virtual function bit is_supported(riscv_instr_gen_config cfg);
      cva6_instr_gen_config_c cfg_cva6;
      `DV_CHECK_FATAL($cast(cfg_cva6, cfg), "Could not cast cfg into cfg_cva6")
      return cfg_cva6.enable_x_extension && (
             instr_name inside {
                CUS_ADD, CUS_ADD_MULTI, CUS_NOP, CUS_ADD_RS3,
                CUS_EXC, CUS_U_ADD, CUS_S_ADD
                               });
   endfunction

endclass

`endif // __CVXIF_CUSTOM_INSTR_SV__
