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

`ifndef __RISCV_ZCMP_INSTR_SV__
`define __RISCV_ZCMP_INSTR_SV__

/**
 * This class describe Zcmp extension.
 */
class riscv_zcmp_instr_c extends riscv_instr;

   `uvm_object_utils(riscv_zcmp_instr_c)

  rand int stack_adj;

  riscv_reg_t                reg_list;
  rand bit [3:0]             rlist;

  bit                        has_reglist = 1'b1;

  function new(string name = "");
    super.new(name);
    rs1 = S0;
    rs2 = S1;
    is_compressed = 1'b1;
  endfunction : new

  constraint rvc_rx_c {
    // Registers specified by the three-bit rs1’, rs2’, and rd’
      if (instr_name inside {CM_MVA01S, CM_MVSA01}) {
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
  }

  constraint reg_list_c {
     if (instr_name inside {CM_PUSH, CM_POP, CM_POPRET, CM_POPRETZ}) {
       // Set the stack_adj depends on the rlist field
       if (rlist inside {[4:7]}) {
         stack_adj == 16 + imm[5:4] * 16;
       }
       if (rlist inside {[8:11]}) {
         stack_adj == 32 + imm[5:4] * 16;
       }
       if (rlist inside {[12:14]}) {
         stack_adj == 48 + imm[5:4] * 16;
       }
       if (rlist == 15) {
         stack_adj == 64 + imm[5:4] * 16;
       }
     }
     if (instr_name inside {CM_MVA01S, CM_MVSA01}) {
       // rs1 & rs2 should be a S-register & different
        rs1 != rs2;
        rs1 inside {S0, S1, [S2:S7]};
        rs2 inside {S0, S1, [S2:S7]};
     }
   }

  constraint zcmp_rlist_c {
    // Constraint register number & imm field
     if (instr_name inside {CM_PUSH, CM_POP, CM_POPRET, CM_POPRETZ}) {
       !(rlist inside {[0:3]});
       imm[31:6] == 0;
       imm[3:0] == 0;
     }
    }

  virtual function void set_imm_len();
    if (instr_name inside {CM_PUSH, CM_POP, CM_POPRET, CM_POPRETZ}) begin
      imm_len = 2;
    end
  endfunction : set_imm_len

   // Convert the instruction to assembly code
   virtual function string convert2asm(string prefix = "");
      string asm_str;
      asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
      if (has_reglist) begin
        if (rlist == 4) begin
          case (instr_name)
            CM_PUSH:        asm_str = $sformatf("%0s{%0s}, %0d",        asm_str, all_gpr[1].name(), -stack_adj);
            CM_POP:         asm_str = $sformatf("%0s{%0s}, %0d",        asm_str, all_gpr[1].name(), stack_adj);
            CM_POPRET:      asm_str = $sformatf("%0s{%0s}, %0d",        asm_str, all_gpr[1].name(), stack_adj);
            CM_POPRETZ:     asm_str = $sformatf("%0s{%0s}, %0d",        asm_str, all_gpr[1].name(), stack_adj);
          endcase
        end
        if (rlist == 5) begin
          case (instr_name)
            CM_PUSH:        asm_str = $sformatf("%0s{%0s, %0s}, %0d",    asm_str, all_gpr[1].name(), all_gpr[8].name(), -stack_adj);
            CM_POP:         asm_str = $sformatf("%0s{%0s, %0s}, %0d",    asm_str, all_gpr[1].name(), all_gpr[8].name(), stack_adj);
            CM_POPRET:      asm_str = $sformatf("%0s{%0s, %0s}, %0d",    asm_str, all_gpr[1].name(), all_gpr[8].name(), stack_adj);
            CM_POPRETZ:     asm_str = $sformatf("%0s{%0s, %0s}, %0d",    asm_str, all_gpr[1].name(), all_gpr[8].name(), stack_adj);
          endcase
        end
        if (rlist == 6) begin
          case (instr_name)
             CM_PUSH:       asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[9].name(), -stack_adj);
             CM_POP:        asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[9].name(), stack_adj);
             CM_POPRET:     asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[9].name(), stack_adj);
             CM_POPRETZ:    asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[9].name(), stack_adj);
          endcase
        end
        if (rlist > 6 && rlist != 15) begin
          case (instr_name)
             CM_PUSH:       asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[rlist+11].name(), -stack_adj);
             CM_POP:        asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[rlist+11].name(), stack_adj);
             CM_POPRET:     asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[rlist+11].name(), stack_adj);
             CM_POPRETZ:    asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[rlist+11].name(), stack_adj);
          endcase
        end
        if (rlist == 15) begin
          case (instr_name)
             CM_PUSH:       asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[27].name(), -stack_adj);
             CM_POP:        asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[27].name(), stack_adj);
             CM_POPRET:     asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[27].name(), stack_adj);
             CM_POPRETZ:    asm_str = $sformatf("%0s{%0s, %0s-%0s}, %0d",  asm_str, all_gpr[1].name(), all_gpr[8].name(), all_gpr[27].name(), stack_adj);
          endcase
        end
      end
      else begin
        case (instr_name)
           CM_MVA01S:       asm_str = $sformatf("%0s%0s, %0s",           asm_str, rs1.name(),  rs2.name());
           CM_MVSA01:       asm_str = $sformatf("%0s%0s, %0s",           asm_str, rs1.name(),  rs2.name());
        endcase
      end
      return asm_str.tolower();
   endfunction : convert2asm

 // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary;
    case (instr_name) inside
      CM_PUSH:
        binary = $sformatf("0x%4h", {get_func6(), get_func2(), rlist, imm[5:4], get_c_opcode()});
      CM_POP:
        binary = $sformatf("0x%4h", {get_func6(), get_func2(), rlist, imm[5:4], get_c_opcode()});
      CM_POPRET:
        binary = $sformatf("0x%4h", {get_func6(), get_func2(), rlist, imm[5:4], get_c_opcode()});
      CM_POPRETZ:
        binary = $sformatf("0x%4h", {get_func6(), get_func2(), rlist, imm[5:4], get_c_opcode()});
      CM_MVA01S:
        binary = $sformatf("0x%4h", {get_func6(), rs1, 2'b11, rs2, get_c_opcode()});
      CM_MVSA01:
        binary = $sformatf("0x%4h", {get_func6(), rs1, 2'b01, rs2, get_c_opcode()});
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
    return {prefix, binary};
  endfunction : convert2bin

  virtual function bit [1:0] get_c_opcode();
    case (instr_name) inside
      CM_PUSH, CM_POP,
      CM_POPRET, CM_POPRETZ,
      CM_MVA01S, CM_MVSA01               : get_c_opcode = 2'b10;
    endcase
  endfunction

   virtual function bit [5:0] get_func6();
      case (instr_name) inside
         CM_PUSH, CM_POP                 : get_func6 = 6'b101110;
         CM_POPRET, CM_POPRETZ           : get_func6 = 6'b101111;
         CM_MVA01S, CM_MVSA01            : get_func6 = 6'b101011;
      endcase
   endfunction

   virtual function bit [1:0] get_func2();
      case (instr_name) inside
         CM_POP, CM_POPRET               : get_func2 = 2'b10;
         CM_PUSH, CM_POPRETZ             : get_func2 = 2'b00;
      endcase
   endfunction

   virtual function void set_rand_mode();
      case (instr_name) inside
         CM_PUSH, CM_POP,
         CM_POPRET, CM_POPRETZ : begin
            has_rd   = 1'b0;
            has_rs1  = 1'b0;
            has_rs2  = 1'b0;
         end
         CM_MVA01S, CM_MVSA01 : begin
            has_rd   = 1'b0;
            has_imm  = 1'b0;
            has_reglist  = 1'b0;
         end
      endcase
   endfunction

   function void pre_randomize();
      rd.rand_mode(has_rd);
      rs1.rand_mode(has_rs1);
      rs2.rand_mode(has_rs2);
      imm.rand_mode(has_imm);
      rlist.rand_mode(has_reglist);
   endfunction

   virtual function bit is_supported(riscv_instr_gen_config cfg);
      cva6_instr_gen_config_c cfg_cva6;
      `DV_CHECK_FATAL($cast(cfg_cva6, cfg), "Could not cast cfg into cfg_cva6")
      return cfg_cva6.enable_zcmp_extension && (
             instr_name inside {
                CM_PUSH, CM_POP,
                CM_POPRET, CM_POPRETZ,
                CM_MVA01S, CM_MVSA01
                               });
   endfunction

endclass

`endif // __RISCV_ZCMP_INSTR_SV__
