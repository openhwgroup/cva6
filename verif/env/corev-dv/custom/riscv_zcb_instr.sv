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
class riscv_zcb_instr_c extends riscv_instr;

   `uvm_object_utils(riscv_zcb_instr_c)

  function new(string name = "");
    super.new(name);
    rs1 = S0;
    rs2 = S0;
    rd  = S0;
    is_compressed = 1'b1;
  endfunction : new

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
         C_LBU    :       asm_str = $sformatf("%0s%0s, %0s(%0s)",      asm_str, rd.name(), get_imm(), rs1.name());
         C_LH     :       asm_str = $sformatf("%0s%0s, %0s(%0s)",      asm_str, rd.name(), get_imm(), rs1.name());
         C_LHU    :       asm_str = $sformatf("%0s%0s, %0s(%0s)",      asm_str, rd.name(), get_imm(), rs1.name());
         C_SB     :       asm_str = $sformatf("%0s%0s, %0s(%0s)",      asm_str, rs2.name(), get_imm(), rs1.name());
         C_SH     :       asm_str = $sformatf("%0s%0s, %0s(%0s)",      asm_str, rs2.name(), get_imm(), rs1.name());
         C_MUL    :       asm_str = $sformatf("%0s%0s, %0s",           asm_str, rd.name(),  rs2.name());
         C_ZEXT_B :       asm_str = $sformatf("%0s%0s",                asm_str, rd.name());
         C_SEXT_B :       asm_str = $sformatf("%0s%0s",                asm_str, rd.name());
         C_ZEXT_H :       asm_str = $sformatf("%0s%0s",                asm_str, rd.name());
         C_SEXT_H :       asm_str = $sformatf("%0s%0s",                asm_str, rd.name());
         C_ZEXT_W :       asm_str = $sformatf("%0s%0s",                asm_str, rd.name());
         C_NOT    :       asm_str = $sformatf("%0s%0s",                asm_str, rd.name());
      endcase
      return asm_str.tolower();
   endfunction : convert2asm

 // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary;
    case (instr_name) inside
      //`uvm_info(`gfn, $sformatf("rs1 = %0s, imm = %b,
      C_LBU:
        binary = $sformatf("0x%4h", {get_func6(), rs1, imm[0], imm[1], rd, get_c_opcode()});
      C_LHU:
        binary = $sformatf("0x%4h", {get_func6(), rs1, 1'b0, imm[1], rd, get_c_opcode()});
      C_LH:
        binary = $sformatf("0x%4h", {get_func6(), rs1 , 1'b1, imm[1],rd , get_c_opcode()});
      C_SB:
        binary = $sformatf("0x%4h", {get_func6(), rs1, imm[0], imm[1] ,rs2 , get_c_opcode()});
      C_SH:
        binary = $sformatf("0x%4h", {get_func6(), rs1, 1'b0, imm[1], rs2, get_c_opcode()});
      C_ZEXT_B:
        binary = $sformatf("0x%4h", {get_func6(), rd, 5'b11000, get_c_opcode()});
      C_SEXT_B:
        binary = $sformatf("0x%4h", {get_func6(), rd, 5'b11001, get_c_opcode()});
      C_ZEXT_H:
        binary = $sformatf("0x%4h", {get_func6(), rd, 5'b11010, get_c_opcode()});
      C_SEXT_H:
        binary = $sformatf("0x%4h", {get_func6(), rd, 5'b11011, get_c_opcode()});
      C_ZEXT_W:
        binary = $sformatf("0x%4h", {get_func6(), rd, 5'b11100, get_c_opcode()});
      C_NOT:
        binary = $sformatf("0x%4h", {get_func6(), rd, 5'b11101, get_c_opcode()});
      C_MUL:
        binary = $sformatf("0x%4h", {get_func6(), rd, 2'b10, rs2, get_c_opcode()});
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
    return {prefix, binary};
  endfunction : convert2bin

  virtual function bit [1:0] get_c_opcode();
    case (instr_name) inside
      C_LBU,C_LH,C_LHU,C_SB,C_SH                      : get_c_opcode = 2'b00;
      C_MUL,C_ZEXT_B,C_SEXT_B,
      C_SEXT_H,C_ZEXT_H,C_ZEXT_W                      : get_c_opcode = 2'b01;
    endcase
  endfunction

   virtual function bit [5:0] get_func6();
      case (instr_name) inside
         C_LBU                  : get_func6 = 6'b100000;
         C_LH                   : get_func6 = 6'b100001;
         C_LHU                  : get_func6 = 6'b100001;
         C_SB                   : get_func6 = 6'b100010;
         C_SH                   : get_func6 = 6'b100011;
         C_MUL                  : get_func6 = 6'b100111;
         C_ZEXT_B               : get_func6 = 6'b100111;
         C_SEXT_B               : get_func6 = 6'b100111;
         C_ZEXT_H               : get_func6 = 6'b100111;
         C_SEXT_H               : get_func6 = 6'b100111;
         C_ZEXT_W               : get_func6 = 6'b100111;
         C_NOT                  : get_func6 = 6'b100111;
      endcase
   endfunction

   virtual function void set_rand_mode();
      case (instr_name) inside
         C_LBU, C_LH, C_LHU : begin
            has_rs2 = 1'b0;
         end
         C_SB, C_SH : begin
            has_rd  = 1'b0;
         end
         C_MUL : begin
            has_rs1  = 1'b0;
            has_imm  = 1'b0;
         end
         C_ZEXT_B, C_SEXT_B,
         C_ZEXT_H, C_SEXT_H,
         C_NOT,C_ZEXT_W  : begin
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
                C_SEXT_H,
                C_NOT,C_ZEXT_W 
                               });
   endfunction

endclass

`endif // __RISCV_ZCB_INSTR_SV__
