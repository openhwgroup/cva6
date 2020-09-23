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

  virtual function void gen_interrupt_vector_table(int              hart,
                                                   string           mode,
                                                   privileged_reg_t status,
                                                   privileged_reg_t cause,
                                                   privileged_reg_t ie,
                                                   privileged_reg_t ip,
                                                   privileged_reg_t scratch,
                                                   ref string       instr[$]);
    // In vector mode, the BASE address is shared between interrupt 0 and exception handling.
    // When vectored interrupts are enabled, interrupt cause 0, which corresponds to user-mode
    // software interrupts, are vectored to the same location as synchronous exceptions. This
    // ambiguity does not arise in practice, since user-mode software interrupts are either
    // disabled or delegated
    corev_instr_gen_config corev_cfg;
    `DV_CHECK_FATAL($cast(corev_cfg, cfg), "Could not cast cfg into corev_cfg")

    instr = {instr, ".option norvc;",
                    $sformatf("j %0s%0smode_exception_handler", hart_prefix(hart), mode)};
    // Redirect the interrupt to the corresponding interrupt handler
    for (int i = 1; i < max_interrupt_vector_num; i++) begin
      instr.push_back($sformatf("j %0s%0smode_intr_vector_%0d", hart_prefix(hart), mode, i));      
    end
    if (!cfg.disable_compressed_instr) begin
      instr = {instr, ".option rvc;"};
    end
    for (int i = 1; i < max_interrupt_vector_num; i++) begin      
      string intr_handler[$];

      if (corev_cfg.use_fast_intr_handler[i]) begin
        // Emit fast interrupt handler that might read a couple of CSRs and finish
        // Save 
        intr_handler.push_back("mret");
      end
      else begin
        // Standard full-stack-save interrupt handler
        push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, intr_handler);
        gen_signature_handshake(.instr(intr_handler), .signature_type(CORE_STATUS),
                                .core_status(HANDLING_IRQ));
        intr_handler = {intr_handler,
                        $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause.name()),
                        // Terminate the test if xCause[31] != 0 (indicating exception)
                        $sformatf("srli x%0d, x%0d, 0x%0x", cfg.gpr[0], cfg.gpr[0], XLEN-1),
                        $sformatf("beqz x%0d, 1f", cfg.gpr[0])};
        gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(status));
        gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(cause));
        gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(ie));
        gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(ip));
        // Jump to commmon interrupt handling routine
        intr_handler = {intr_handler,
                        $sformatf("j %0s%0smode_intr_handler", hart_prefix(hart), mode),
                        "1: j test_done"};
      end

      gen_section(get_label($sformatf("%0smode_intr_vector_%0d", mode, i), hart), intr_handler);
    end
  endfunction : gen_interrupt_vector_table

  // Setup EPC before entering target privileged mode
  virtual function void setup_epc(int hart);
    string instr[$];
    string mode_name;
    instr = {$sformatf("la x%0d, %0sinit", cfg.gpr[0], hart_prefix(hart))};
    if(cfg.virtual_addr_translation_on) begin
      // For supervisor and user mode, use virtual address instead of physical address.
      // Virtual address starts from address 0x0, here only the lower 12 bits are kept
      // as virtual address offset.
      instr = {instr,
               $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 12),
               $sformatf("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 12)};
    end
    mode_name = cfg.init_privileged_mode.name();
    instr.push_back($sformatf("csrw mepc, x%0d", cfg.gpr[0]));
    if (!riscv_instr_pkg::support_pmp) begin
      instr.push_back($sformatf("jal ra, %0sinit_%0s", hart_prefix(hart), mode_name.tolower()));
    end
    gen_section(get_label("mepc_setup", hart), instr);
  endfunction

  // Interrupt handler routine
  // Override from risc-dv since interrupts are auto-cleared, mip will not track through the ISS 
  // to GPR properly with autoclear
  virtual function void gen_interrupt_handler_section(privileged_mode_t mode, int hart);
    string mode_prefix;
    string ls_unit;
    privileged_reg_t status, ip, ie, scratch;
    string interrupt_handler_instr[$];
    ls_unit = (XLEN == 32) ? "w" : "d";
    if (mode < cfg.init_privileged_mode) return;
    if (mode == USER_MODE && !riscv_instr_pkg::support_umode_trap) return;
    case(mode)
      MACHINE_MODE: begin
        mode_prefix = "m";
        status = MSTATUS;
        ip = MIP;
        ie = MIE;
        scratch = MSCRATCH;
      end
      SUPERVISOR_MODE: begin
        mode_prefix = "s";
        status = SSTATUS;
        ip = SIP;
        ie = SIE;
        scratch = SSCRATCH;
      end
      USER_MODE: begin
        mode_prefix = "u";
        status = USTATUS;
        ip = UIP;
        ie = UIE;
        scratch = USCRATCH;
      end
      default: `uvm_fatal(get_full_name(), $sformatf("Unsupported mode: %0s", mode.name()))
    endcase
      // If nested interrupts are enabled, set xSTATUS.xIE in the interrupt handler
      // to re-enable interrupt handling capabilities
      if (cfg.enable_nested_interrupt) begin
        interrupt_handler_instr.push_back($sformatf("csrr x%0d, 0x%0x", cfg.gpr[0], scratch));
        interrupt_handler_instr.push_back($sformatf("bgtz x%0d, 1f", cfg.gpr[0]));
        interrupt_handler_instr.push_back($sformatf("csrwi 0x%0x, 0x1", scratch));
        case (status)
          MSTATUS: begin
            interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 8));
          end
          SSTATUS: begin
            interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 2));
          end
          USTATUS: begin
            interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 1));
          end
          default: `uvm_fatal(`gfn, $sformatf("Unsupported status %0s", status))
        endcase
        interrupt_handler_instr.push_back($sformatf("1: csrwi 0x%0x,0", scratch));
      end
    // Read back interrupt related privileged CSR
    // The value of these CSR are checked by comparing with spike simulation result.
    interrupt_handler_instr = {
           interrupt_handler_instr,
           $sformatf("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], status, status.name()),
           $sformatf("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], ie, ie.name())
    };
    gen_plic_section(interrupt_handler_instr);
    // Restore user mode GPR value from kernel stack before return
    pop_gpr_from_kernel_stack(status, scratch, cfg.mstatus_mprv,
                              cfg.sp, cfg.tp, interrupt_handler_instr);
    interrupt_handler_instr = {interrupt_handler_instr,
                               $sformatf("%0sret;", mode_prefix)
    };
    if (SATP_MODE != BARE) begin
      // The interrupt handler will use one 4KB page
      instr_stream.push_back(".align 12");
    end else begin
      instr_stream.push_back(".align 2");
    end
    gen_section(get_label($sformatf("%0smode_intr_handler", mode_prefix), hart),
                interrupt_handler_instr);
  endfunction : gen_interrupt_handler_section

  virtual function void gen_test_done();
    instr_stream.push_back("");
    instr_stream.push_back("#Start: Extracted from riscv_compliance_tests/riscv_test.h");
    instr_stream.push_back("test_done:");
    instr_stream.push_back("                  csrrci x0,mstatus,0x8 # Clear MSTATUS.MIE to avoid interrupts during test_done");
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
