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
// CORE-V instruction generator base test:
//     - extension of the RISC-V instruction generator base test.
//
//------------------------------------------------------------------------------

class cv32e40x_instr_base_test extends corev_instr_base_test;

  cv32e40x_pma_cfg pma_cfg;
  bit enable_pma;

  `uvm_component_utils(cv32e40x_instr_base_test)


  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    cv32e40x_ldgen_c linker_generator;
    override_asm_program_gen();
    override_gen_config();
    override_compressed_instr();
    override_privil_reg();
    override_privil_common_seq();
    override_debug_rom_gen();
    super.build_phase(phase);
    linker_generator = new();
    linker_generator.gen_pma_linker_scripts();
  endfunction

  virtual function void override_asm_program_gen();
    uvm_factory::get().set_type_override_by_type(corev_asm_program_gen::get_type(),
                                                 cv32e40x_asm_program_gen::get_type());
  endfunction

  virtual function void override_gen_config();
    uvm_factory::get().set_type_override_by_type(riscv_instr_gen_config::get_type(),
                                                 cv32e40x_instr_gen_config::get_type());
  endfunction

  virtual function void override_compressed_instr();
    uvm_factory::get().set_type_override_by_type(riscv_C_LUI_instr::get_type(),
                                                 cv32e40x_C_LUI_instr::get_type());
  endfunction

  virtual function void override_privil_reg();
    uvm_factory::get().set_type_override_by_type(riscv_privil_reg::get_type(),
                                                 cv32e40x_privil_reg::get_type());
  endfunction

  virtual function void override_privil_common_seq();
    uvm_factory::get().set_type_override_by_type(riscv_privileged_common_seq::get_type(),
                                                 cv32e40x_privileged_common_seq::get_type());
  endfunction

  virtual function void override_debug_rom_gen();
    uvm_factory::get().set_type_override_by_type(riscv_debug_rom_gen::get_type(),
                                                 cv32e40x_debug_rom_gen::get_type());
  endfunction

  virtual function void apply_directed_instr();
  endfunction

endclass : cv32e40x_instr_base_test
