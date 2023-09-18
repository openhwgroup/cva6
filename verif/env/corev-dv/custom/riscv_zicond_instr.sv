// Copyright 2023 Thales
// Copyright 2023 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)
// ------------------------------------------------------------------------------ //

`ifndef __RISCV_ZICOND_INSTR_SV__
`define __RISCV_ZICOND_INSTR_SV__

/**
 * This class describe Zicond extension.
 */
class riscv_zicond_instr_c extends riscv_custom_instr;

   `uvm_object_utils(riscv_zicond_instr_c)
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
         CZERO_EQZ:       asm_str = $sformatf("%0s %0s, %0s, %0s",      asm_str, rd.name(),  rs1.name(),  rs2.name());
         CZERO_NEZ:       asm_str = $sformatf("%0s %0s, %0s, %0s",      asm_str, rd.name(),  rs1.name(),  rs2.name());
      endcase
      return asm_str.tolower();
   endfunction : convert2asm

  virtual function bit [6:0] get_opcode();
    case (instr_name) inside
      CZERO_EQZ,
      CZERO_NEZ                     : get_opcode = 7'b0110011;
    endcase
  endfunction

   virtual function bit [2:0] get_func3();
      case (instr_name) inside
         CZERO_EQZ                  : get_func3 = 3'b101;
         CZERO_NEZ                  : get_func3 = 3'b111;
      endcase
   endfunction

   virtual function bit [6:0] get_func7();
      case (instr_name)
         CZERO_EQZ,
         CZERO_NEZ                   : get_func7 = 7'b0000111;
      endcase
   endfunction

   function void pre_randomize();
      rd.rand_mode(has_rd);
      rs1.rand_mode(has_rs1);
      rs2.rand_mode(has_rs2);
   endfunction

   virtual function bit is_supported(riscv_instr_gen_config cfg);
      cva6_instr_gen_config_c cfg_cva6;
      `DV_CHECK_FATAL($cast(cfg_cva6, cfg), "Could not cast cfg into cfg_cva6")
      return cfg_cva6.enable_zicond_extension && (
             instr_name inside {
                CZERO_EQZ,
                CZERO_NEZ
                               });
   endfunction

endclass

`endif // __RISCV_ZICOND_INSTR_SV__
