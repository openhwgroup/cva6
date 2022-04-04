/*
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

package cv32e40x_instr_test_pkg;

  import uvm_pkg::*;
  import riscv_instr_pkg::*;
  import riscv_instr_test_pkg::*;
  import riscv_signature_pkg::*;
  import corev_instr_test_pkg::*;

  import cv32e40x_pkg::pma_region_t;

  `include "uvmt_cv32e40x_constants.sv"
  `include "pma_adapted_mem_region_gen.sv"
  `include "cv32e40x_ldgen.sv"

  // Instruction streams specific to CV32E40X

  // RISCV-DV class override definitions
  `include "cv32e40x_pma_cfg.sv"
  `include "cv32e40x_compressed_instr.sv"
  `include "cv32e40x_privil_reg.sv"
  `include "cv32e40x_privileged_common_seq.sv"
  `include "cv32e40x_instr_gen_config.sv"
  `include "cv32e40x_debug_rom_gen.sv"
  `include "cv32e40x_asm_program_gen.sv"
  `include "cv32e40x_instr_base_test.sv"
  `include "cv32e40x_pma_instr_lib.sv"
  `include "cv32e40x_fencei_instr_lib.sv"

  // Push general purpose register to the debugger stack
  function automatic void push_gpr_to_debugger_stack(cv32e40x_instr_gen_config cfg_corev,
                                                     ref string instr[$]);
    string store_instr = (XLEN == 32) ? "sw" : "sd";
    // Reserve space from kernel stack to save all 32 GPR except for x0
    instr.push_back($sformatf("1: addi x%0d, x%0d, -%0d", cfg_corev.dp, cfg_corev.dp, 31 * (XLEN/8)));
    // Push all GPRs to kernel stack
    for(int i = 1; i < 32; i++) begin
      if (i == cfg_corev.dp) continue;
      if (i == cfg_corev.sp) continue;
      if (i == cfg_corev.tp) continue;
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, i, i * (XLEN/8), cfg_corev.dp));
    end
  endfunction : push_gpr_to_debugger_stack

    // Pop general purpose register from debugger stack
  function automatic void pop_gpr_from_debugger_stack(cv32e40x_instr_gen_config cfg_corev,
                                                      ref string instr[$]);
    string load_instr = (XLEN == 32) ? "lw" : "ld";
    // Pop user mode GPRs from kernel stack
    for(int i = 1; i < 32; i++) begin
      if (i == cfg_corev.dp) continue;
      if (i == cfg_corev.sp) continue;
      if (i == cfg_corev.tp) continue;
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, i, i * (XLEN/8), cfg_corev.dp));
    end
    // Restore debugger stack pointer
    instr.push_back($sformatf("addi x%0d, x%0d, %0d", cfg_corev.dp, cfg_corev.dp, 31 * (XLEN/8)));
  endfunction : pop_gpr_from_debugger_stack

endpackage : cv32e40x_instr_test_pkg;
