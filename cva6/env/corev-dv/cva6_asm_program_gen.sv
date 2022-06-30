/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
 * Copyright 2020 OpenHW Group
 * Copyright 2022 Thales DIS design services SAS
 *
 * Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
 *
 * You may obtain a copy of the License at
 *      https://solderpad.org/licenses/
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


`ifndef __CVA6_ASM_PROGRAM_GEN_SV__
`define __CVA6_ASM_PROGRAM_GEN_SV__

//-----------------------------------------------------------------------------------------
// CVA6 assembly program generator - extension of the RISC-V assembly program generator.
//
// Overrides gen_program_header()
//-----------------------------------------------------------------------------------------

class cva6_asm_program_gen_c extends riscv_asm_program_gen;

   `uvm_object_utils(cva6_asm_program_gen_c)

   function new (string name = "");
      super.new(name);
   endfunction

   virtual function void gen_program_header();
      string str[$];
      instr_stream.push_back(".include \"user_define.include\"");
      instr_stream.push_back(".globl _start");
      instr_stream.push_back(".section .text");
      if (cfg.disable_compressed_instr) begin
         instr_stream.push_back(".option norvc;");
      end
      str = {"csrr x5, mhartid"};
      for (int hart = 0; hart < cfg.num_of_harts; hart++) begin
         str = {str, $sformatf("li x6, %0d", hart),
                     $sformatf("beq x5, x6, %0df", hart)};
      end
      gen_section("_start", str);
      for (int hart = 0; hart < cfg.num_of_harts; hart++) begin
         instr_stream.push_back($sformatf("%0d: j h%0d_start", hart, hart));
      end
   endfunction

endclass : cva6_asm_program_gen_c

`endif // __CVA6_ASM_PROGRAM_GEN_SV__
