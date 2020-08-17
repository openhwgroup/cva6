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
// CORE-V instruction generator configuration class:
//     - extension of the RISC-V instruction generator base test.
//
// The base test Uses the factory to replace riscv_instr_gen_config with corev_instr_gen_config
//------------------------------------------------------------------------------

class corev_instr_gen_config extends riscv_instr_gen_config;

  // CV32E40P requires the MTVEC table to be aligned to 256KB boundaries
  constraint mtvec_c {    
    tvec_alignment == 8;
  }

  `uvm_object_utils(corev_instr_gen_config)

  function new(string name="");
    super.new(name);
  endfunction

endclass
