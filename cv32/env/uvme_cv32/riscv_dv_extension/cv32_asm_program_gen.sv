//
// Copyright 2020 OpenHW Group
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
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

`ifndef __CV32E40P_ASM_PROGRAM_GEN__
`define __CV32E40P_ASM_PROGRAM_GEN__

//-----------------------------------------------------------------------------------------
// RISC-V assembly program generator for cv32e40p
// Adapted from ibex_asm_program_gen for IBEX (see https://github.com/lowRISC/ibex)
//-----------------------------------------------------------------------------------------

class cv32e40p_asm_program_gen extends riscv_asm_program_gen;

  `uvm_object_utils(cv32e40p_asm_program_gen)
  `uvm_object_new

  virtual function void gen_program_header();
    // Override the cfg value, below fields are not supported by ibex
    cfg.mstatus_mprv = 0;
    cfg.mstatus_mxr  = 0;
    cfg.mstatus_sum  = 0;
    cfg.mstatus_tvm  = 0;
    cfg.check_misa_init_val = 1'b0;
    cfg.check_xstatus = 1'b0;
    
    instr_stream.push_back(".section .text");
    instr_stream.push_back(".globl _start");
    instr_stream.push_back(".option norvc");
    // 0x0 debug mode entry
    instr_stream.push_back("j debug_rom");
    // 0x4 debug mode exception handler
    instr_stream.push_back("j debug_exception");
    // Align the start section to 0x80
    instr_stream.push_back(".align 7");
    instr_stream.push_back(".option rvc");
    instr_stream.push_back("_start:");
  endfunction

endclass

`endif // __CV32E40P_ASM_PROGRAM_GEN__
