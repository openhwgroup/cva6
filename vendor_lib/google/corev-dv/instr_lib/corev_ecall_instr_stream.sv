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

