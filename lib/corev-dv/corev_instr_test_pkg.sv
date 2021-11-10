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

package corev_instr_test_pkg;

  import uvm_pkg::*;
  import riscv_instr_pkg::*;
  import riscv_instr_test_pkg::*;
  import riscv_signature_pkg::*;

  // Instruction streams
  `include "instr_lib/corev_interrupt_csr_instr_stream.sv"
  `include "instr_lib/corev_interrupt_csr_wfi_instr_stream.sv"
  `include "instr_lib/corev_compressed_load_store_stress_instr_stream.sv"
  `include "instr_lib/corev_compressed_load_store_wfi_stress_instr_stream.sv"
  `include "instr_lib/corev_ecall_instr_stream.sv"
  `include "instr_lib/corev_nop_instr.sv"
  `include "instr_lib/corev_xori_not_instr.sv"
  `include "instr_lib/corev_jal_wfi_instr.sv"
  `include "instr_lib/corev_jalr_wfi_instr.sv"

  `include "corev_asm_program_gen.sv"
  `include "corev_report_server.sv"
  `include "corev_instr_base_test.sv"
  `include "corev_directive_instr.sv"

endpackage : corev_instr_test_pkg;
