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
 * corev_jal_wfi_instr
 *
 * corev_jal_wfi_instr: Directed test stream that uses the riscv_jal_instr directed instruction stream and injects random
 * WFI instructions in the stream.  This helps to close coverage on WFI combination instructions with C_J and JAL instructions
 */

class corev_jal_wfi_instr extends riscv_jal_instr;

  rand int unsigned num_wfi;

  constraint num_wfi_c {
    num_wfi inside {[0:3]};
  }

  `uvm_object_utils(corev_jal_wfi_instr);

  function new(string name = "");
    super.new(name);
  endfunction : new
  
  function void post_randomize();
    int unsigned next_label;

    super.post_randomize();

    next_label = num_of_jump_instr + 1;

    foreach (instr_list[i]) begin
      instr_list[i].atomic = 0;
    end

    for (int i = 0; i < num_wfi; i++) begin
      riscv_instr instr;

      instr = riscv_instr::get_rand_instr(.include_instr({WFI}));
      instr.comment = "corev_jal_wfi_instr";
      instr.label = $sformatf("%0d", next_label++);

      // Randomly insert
      insert_instr(instr);
    end

    // Go through list of jumps now and add in labels for WFI followed by non-WFI
    for (int i = 0; i < instr_list.size(); i++) begin
      // Set all instructions as atomic, other streams may not interrupt this instruction block
      instr_list[i].atomic = 1;

      // If a WFI is followed by a Jump, move the jump target to the WFI and cre4ate a dummy label for the next instruction
      if (i + 1 < instr_list.size()) begin
        if (instr_list[i].instr_name == WFI && instr_list[i+1].instr_name != WFI) begin
          instr_list[i].label = instr_list[i+1].label;
          instr_list[i+1].label = $sformatf("%0d", next_label++); 
        end
      end
    end

  endfunction : post_randomize

endclass : corev_jal_wfi_instr
