// Copyright 2023 Thales DIS
// Copyright 2023 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)
// ------------------------------------------------------------------------------ //

`ifndef __RISCV_ZCB_INSTR_SV__
`define __RISCV_ZCB_INSTR_SV__

/**
 * This class describe Zcb extension.
 */
class riscv_zcb_instr_c extends riscv_custom_instr;

   `uvm_object_utils(riscv_zcb_instr_c)
   `uvm_object_new

  constraint rvc_rx_c {
    //  Registers specified by the three-bit rs1’, rs2’, and rd’
      if (has_rs1) {
        rs1 inside {[S0:A5]};
      }
      if (has_rs2) {
        rs2 inside {[S0:A5]};
      }
      if (has_rd) {
        rd inside {[S0:A5]};
      }
    }

  constraint Zcb_imm_c {
    //  Constraint for immediate field
      if (instr_name inside {C_LHU, C_LH, C_SH}) {
        imm[0] == 1'b0;
      }
    }

   virtual function string get_instr_name();
      get_instr_name = instr_name.name();
      return get_instr_name;
   endfunction : get_instr_name

  virtual function void set_imm_len();
    if (instr_name inside {C_LBU, C_LH, C_LHU, C_SB, C_SH}) begin
      imm_len = 2;
    end
  endfunction : set_imm_len

   // Convert the instruction to assembly code
   virtual function string convert2asm(string prefix = "");
      string asm_str;
      asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
      case (instr_name)
         C_LBU    :       asm_str = $sformatf("%0s %0s, %0s(%0s)",      asm_str, rd.name(), get_imm(), rs1.name());
         C_LH     :       asm_str = $sformatf("%0s %0s, %0s(%0s)",      asm_str, rd.name(), get_imm(), rs1.name());
         C_LHU    :       asm_str = $sformatf("%0s %0s, %0s(%0s)",      asm_str, rd.name(), get_imm(), rs1.name());
         C_SB     :       asm_str = $sformatf("%0s %0s, %0s(%0s)",      asm_str, rs2.name(), get_imm(), rs1.name());
         C_SH     :       asm_str = $sformatf("%0s %0s, %0s(%0s)",      asm_str, rs2.name(), get_imm(), rs1.name());
         C_MUL    :       asm_str = $sformatf("%0s %0s, %0s",           asm_str, rd.name(),  rs2.name());
         C_ZEXT_B :       asm_str = $sformatf("%0s %0s",                asm_str, rd.name());
         C_SEXT_B :       asm_str = $sformatf("%0s %0s",                asm_str, rd.name());
         C_ZEXT_H :       asm_str = $sformatf("%0s %0s",                asm_str, rd.name());
         C_SEXT_H :       asm_str = $sformatf("%0s %0s",                asm_str, rd.name());
         C_ZEXT_W :       asm_str = $sformatf("%0s %0s",                asm_str, rd.name());
         C_NOT    :       asm_str = $sformatf("%0s %0s",                asm_str, rd.name());
      endcase
      return asm_str.tolower();
   endfunction : convert2asm

  virtual function bit [1:0] get_c_opcode();
    case (instr_name) inside
      C_LBU,C_LH,C_LHU,C_SB,C_SH                      : get_c_opcode = 2'b00;
      C_MUL,C_ZEXT_B,C_SEXT_B,C_ZEXT_H,
      C_SEXT_H,C_ZEXT_W                               : get_c_opcode = 2'b01;
    endcase
  endfunction

   virtual function bit [2:0] get_func3();
      case (instr_name) inside
         C_LBU                  : get_func3 = 3'b100;
         C_LH                   : get_func3 = 3'b100;
         C_LHU                  : get_func3 = 3'b100;
         C_SB                   : get_func3 = 3'b100;
         C_SH                   : get_func3 = 3'b100;
         C_MUL                  : get_func3 = 3'b100;
         C_ZEXT_B               : get_func3 = 3'b100;
         C_SEXT_B               : get_func3 = 3'b100;
         C_ZEXT_H               : get_func3 = 3'b100;
         C_SEXT_H               : get_func3 = 3'b100;
         C_ZEXT_W               : get_func3 = 3'b100;
         C_NOT                  : get_func3 = 3'b100;
      endcase
   endfunction

   virtual function void set_rand_mode();
      case (instr_name) inside
         "C_LBU", "C_LH","C_LHU" : begin
            has_rs2 = 1'b0;
         end
         "C_SB", "C_SH" : begin
            has_rd  = 1'b0;
         end
         "C_MUL" : begin
            has_rs1  = 1'b0;
            has_imm  = 1'b0;
         end
         "C_ZEXT_B", "C_SEXT_B",
         "C_ZEXT_H", "C_SEXT_H",
         "C_ZEXT_W", "C_NOT"     : begin
            has_rs1  = 1'b0;
            has_rs2  = 1'b0;
            has_imm  = 1'b0;
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
      return cfg_cva6.enable_zcb_extension && (
             instr_name inside {
                C_LBU,C_LH,C_LHU,C_SB,C_SH,
                C_MUL,
                C_ZEXT_B,C_SEXT_B,C_ZEXT_H,
                C_SEXT_H,C_ZEXT_W,
                C_NOT    
                               });
   endfunction

endclass

`endif // __RISCV_ZICOND_INSTR_SV__
