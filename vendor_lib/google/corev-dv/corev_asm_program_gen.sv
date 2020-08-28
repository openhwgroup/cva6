/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
 * Copyright 2020 OpenHW Group
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------------------
// CORE-V assembly program generator - extension of the RISC-V assembly program generator.
//
// Overrides gen_program_header() and gen_test_done()
//-----------------------------------------------------------------------------------------

class corev_asm_program_gen extends riscv_asm_program_gen;

  `uvm_object_utils(corev_asm_program_gen)

  function new (string name = "");
    super.new(name);
  endfunction


  virtual function void gen_program_header();
    instr_stream.push_back(".include \"user_define.h\"");
    instr_stream.push_back(".section .text.start");
    instr_stream.push_back(".globl _start");
    instr_stream.push_back(".section .init");
    if (cfg.disable_compressed_instr) begin
      instr_stream.push_back(".option norvc;");
    end
    instr_stream.push_back("#.include \"user_init.s\"");
    instr_stream.push_back(".type _start, @function");
    instr_stream.push_back("");
    instr_stream.push_back("_start:");
    instr_stream.push_back("    j _start_main");
    instr_stream.push_back("");
    instr_stream.push_back(".globl _start_main");
    instr_stream.push_back(".section .text");
    instr_stream.push_back("_start_main:");
  endfunction


  virtual function void gen_test_done();
    instr_stream.push_back("");
    instr_stream.push_back("#Start: Extracted from riscv_compliance_tests/riscv_test.h");
    instr_stream.push_back("test_done:");
    instr_stream.push_back("                  lui a0,print_port>>12");
    instr_stream.push_back("                  addi a1,zero,'\\n'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'C'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'V'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'3'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'2'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,' '");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'D'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'O'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'N'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'E'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  addi a1,zero,'\\n'");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("");
    instr_stream.push_back("                  li a0, test_ret_val");
    instr_stream.push_back("                  lw a1, test_results /* report result */");
    instr_stream.push_back("                  sw a1,0(a0)");
    instr_stream.push_back("");
    instr_stream.push_back("                  csrrwi x0,mie,0 /* clear mie so that final wfi never awakens */");
    instr_stream.push_back("                  wfi  /* we are done */");
    instr_stream.push_back("#End: Extracted from riscv_compliance_tests/riscv_test.h");
    instr_stream.push_back("");
  endfunction

endclass
