/*
 * Copyright 2020 OpenHW Group
 * Copyright 2020 Silicon Labs, Inc.
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

 /*
 * corev_interrupt_csr_wfi_instr_stream
 *
 * Directed instruction stream derived from corev_interrupt_csr_instr_stream
 * but ensures that at least one valid CLINT interrupt is set to avoid starving WFI
 */

class corev_interrupt_csr_wfi_instr_stream extends corev_interrupt_csr_instr_stream;

  constraint wfi_c {
    action == RANDOM_MIE -> ((rand_mie_setting & valid_interrupt_mask) != 0);
  }

  `uvm_object_utils(corev_interrupt_csr_wfi_instr_stream)
  `uvm_object_new

  function void post_randomize();
    allowed_mie_instr = {CSRRW};

    // Do not allow zero as destination register for LI (might clear MIE inadvertently)
    reserved_rd = new[reserved_rd.size() + 1](reserved_rd);
    reserved_rd[reserved_rd.size()-1] = ZERO;
    
    super.post_randomize();
  endfunction : post_randomize

endclass : corev_interrupt_csr_wfi_instr_stream
