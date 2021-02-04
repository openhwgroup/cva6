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
// - Uses the factory to replace riscv_asm_program_gen with corev_asm_program_gen.
// - Uses the factory to replace riscv_privil_reg with corev_privil_reg which
//        adds platform-specific fields
//------------------------------------------------------------------------------

class corev_instr_base_test extends riscv_instr_base_test;

  string                  default_asm_file_name = "corev_asm_test";
  string                  asm_file_name_opts;
  string                  asm_file_name;
  corev_asm_program_gen   asm_gen;

  corev_report_server     rs;

  `uvm_component_utils(corev_instr_base_test)

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);

    rs = new("rs");
    uvm_report_server::set_server(rs);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction  

  task run_phase(uvm_phase phase);
    int fd;
    for(int i = 0; i < cfg.num_of_tests; i++) begin
      string test_name;
      randomize_cfg();
      riscv_instr::create_instr_list(cfg);
      asm_gen = corev_asm_program_gen::type_id::create("asm_gen", , `gfn);
      asm_gen.cfg = cfg;
      asm_gen.get_directed_instr_stream();
      if ($value$plusargs("asm_file_name_opts=%s", asm_file_name)) begin
        test_name = $sformatf("%0s_%0d.S", asm_file_name, i+start_idx);
      end
      else begin
        test_name = $sformatf("%0s_%0d.S", default_asm_file_name, i+start_idx);
      end
      apply_directed_instr();
      `uvm_info(`gfn, "All directed instructions are applied", UVM_LOW)
      asm_gen.gen_program();
      `uvm_info(`gfn, $sformatf("Generating %s", test_name), UVM_LOW)
      asm_gen.gen_test_file(test_name);
    end
  endtask

endclass : corev_instr_base_test

