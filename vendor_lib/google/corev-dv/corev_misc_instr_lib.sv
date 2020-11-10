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
 * corev_misc_instr_lib
 *
 * corev_ecall_isntr_stream: Directed test stream to inject ECALL in tests 
 */

 class corev_ecall_instr_stream extends riscv_load_store_rand_instr_stream;
  
  rand int unsigned ecall_cnt;

  constraint ecall_c {
    ecall_cnt inside {[1:5]};    
  }

  `uvm_object_utils(corev_ecall_instr_stream)
  `uvm_object_new
  
  virtual function void add_mixed_instr(int instr_cnt);
    super.add_mixed_instr(instr_cnt);

    add_ecall(ecall_cnt);
  endfunction : add_mixed_instr

  virtual function void add_ecall(int unsigned cnt);
    riscv_instr ecall_instr;

    for (int i = 0; i < cnt; i++) begin
      ecall_instr = riscv_instr::get_rand_instr(.include_instr({ECALL}));
      `DV_CHECK_RANDOMIZE_FATAL(ecall_instr)
      ecall_instr.comment = "corev-dv: corev_ecall_instr_stream";
      insert_instr(ecall_instr);
    end
  endfunction : add_ecall

 endclass : corev_ecall_instr_stream

/*
 * corev_jal_wfi_instr
 *
 * corev_hal_wfi_instr: Directed test stream that uses the riscv_jal_instr directed instruction stream and injects random
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

class corev_nop_instr extends riscv_directed_instr_stream;

  `uvm_object_utils(corev_nop_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr_name_t allowed_nop[$];
    riscv_instr        nop;

    allowed_nop.push_back(NOP);
    if (!cfg.disable_compressed_instr)
      allowed_nop.push_back(C_NOP);

    nop = riscv_instr::get_rand_instr(.include_instr(allowed_nop));
    nop.m_cfg = cfg;
    randomize_gpr(nop);
    insert_instr(nop);
  endfunction : post_randomize

endclass : corev_nop_instr