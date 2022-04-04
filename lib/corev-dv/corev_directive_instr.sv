/*
 * Copyright 2021 OpenHW Group
 * Copyright 2021 Silicon Labs
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

// Not a real instruction but useful for inserting assembler directives into directed instruction streams
class corev_directive_instr extends riscv_instr;

  // Specify the entire assembler directive in the string variable
  // e.g. directive = ".option norvc";
  string directive;

  `uvm_object_utils(corev_directive_instr)

  function new(string name = "");
    super.new(name);
    process_load_store = 0;
  endfunction : new

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;

    asm_str = $sformatf("    %0s", directive);
    if(comment != "")
      asm_str = {asm_str, " #",comment};

    return asm_str.tolower();
  endfunction : convert2asm

  virtual function string get_instr_name();
    return directive;
  endfunction : get_instr_name

endclass : corev_directive_instr
