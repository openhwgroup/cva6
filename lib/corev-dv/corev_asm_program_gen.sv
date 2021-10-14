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
    $display("IN COREV");
  endfunction

  virtual function void gen_program_header();
    instr_stream.push_back(".include \"user_define.h\"");
    instr_stream.push_back(".section .text.start");
    instr_stream.push_back("");

    instr_stream.push_back(".section .mtvec_bootstrap, \"ax\"");
    instr_stream.push_back(".globl _mtvec_bootstrap");
    instr_stream.push_back("    j mtvec_handler");
    instr_stream.push_back("");

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
    instr_stream.push_back(".globl mtvec_handler");
    instr_stream.push_back(".section .text");
    instr_stream.push_back("_start_main:");
  endfunction

  virtual function void gen_test_done();
    // Select two registers to serve as reg0,reg1 in fixed test_done
    // Avoid using the reserved registers

    riscv_reg_t td_reg[2];
    string      td_nam[2];

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(td_reg,
      td_reg[0] != td_reg[1];
      foreach (td_reg[i]) {
        td_reg[i] != ZERO;
        foreach (cfg.reserved_regs[j]) {
          td_reg[i] != cfg.reserved_regs[j];
        }
      }
    )

    td_nam[0] = td_reg[0].name();
    td_nam[1] = td_reg[1].name();

    instr_stream.push_back($sformatf(""));
    instr_stream.push_back($sformatf("#Start: Extracted from riscv_compliance_tests/riscv_test.h"));
    instr_stream.push_back($sformatf("test_done:"));
    instr_stream.push_back($sformatf("                  csrrci x0,mstatus,0x8 # Clear MSTATUS.MIE to avoid interrupts during test_done"));
    instr_stream.push_back($sformatf("                  lui %s,print_port>>12", td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'\\n'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'C'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'V'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'3'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'2'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,' '", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'D'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'O'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'N'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'E'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  addi %s,zero,'\\n'", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf(""));
    instr_stream.push_back($sformatf("                  li %s, test_ret_val", td_nam[0].tolower()));
    instr_stream.push_back($sformatf("                  lw %s, test_results /* report result */", td_nam[1].tolower()));
    instr_stream.push_back($sformatf("                  sw %s,0(%s)", td_nam[1].tolower(), td_nam[0].tolower()));
    instr_stream.push_back($sformatf(""));
    instr_stream.push_back($sformatf("                  csrrwi x0,mie,0 /* clear mie so that final wfi never awakens */"));
    instr_stream.push_back($sformatf("                  wfi  /* we are done */"));
    instr_stream.push_back($sformatf("#End: Extracted from riscv_compliance_tests/riscv_test.h"));
    instr_stream.push_back($sformatf(""));
  endfunction : gen_test_done

  // Therefore to enable random ecalls in test, simply handle ecall as an exception with no special
  // processing other than to increment the PC from MEPC
  virtual function void gen_ecall_handler(int hart);
    string instr[$];
    instr = {instr,
            $sformatf("csrr  x%0d, mepc", cfg.gpr[0]),
            $sformatf("addi  x%0d, x%0d, 4", cfg.gpr[0], cfg.gpr[0]),
            $sformatf("csrw  mepc, x%0d", cfg.gpr[0])
    };
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("ecall_handler", hart), instr);
  endfunction : gen_ecall_handler

endclass : corev_asm_program_gen
