/*
 * Copyright 2018 Google LLC
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

//------------------------------------------------------------------------------
// CORE-V illegal instruction
//     Extends privileged registers for CORE-V core platform extensions
//
// The base test Uses the factory to replace riscv_illegal_instr_reg with corev_illegal_instr
//   - Adds CV32E40P CSRs to ensure illegal instructions do not target proper instructions
//      - NOTE: This is caused by riscv-dv for CV32E40P v1.0.0 using an older riscv-dv that
//              was out of date with respect to debug spec (i.e. missed some CSRs).
//              This should be undone upon upgrading riscv-dv version.
//------------------------------------------------------------------------------

class cv32e40p_illegal_instr extends riscv_illegal_instr;

  constraint missing_csr_debug_regs_c {
    instr_bin[31:20] != 'h7A4; // TINFO
    instr_bin[31:20] != 'h7A5; // TCONTROL
    instr_bin[31:20] != 'h7A8; // MCONTEXT
    instr_bin[31:20] != 'h7AA; // SCONTEXT    
  }

  `uvm_object_utils(cv32e40p_illegal_instr);

  function new(string name="");
    super.new(name);
  endfunction  

endclass : cv32e40p_illegal_instr
