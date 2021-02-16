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
 * corev_load_store instruction sequences
 *
 * corev_compressed_load_store_wfi_stress_instr_stream: Extension of riscv_load_store_rand_instr_stream with offsets
 * biased to generate many C_LW and C_SW streams and injected WFI
 */


class corev_compressed_load_store_wfi_stress_instr_stream extends corev_compressed_load_store_stress_instr_stream;
  
  rand bit first_instr_wfi;
  rand bit last_instr_wfi;  

  constraint wfi_dist_c {
    first_instr_wfi dist { 0 :/ 1, 1 :/ 9};
    last_instr_wfi dist { 0 :/ 1, 1 :/ 9};
  }

  `uvm_object_utils(corev_compressed_load_store_wfi_stress_instr_stream)
  
  function new(string name = "corev_compressed_load_store_wfi_stress_instr_stream");
    super.new(name);

    min_instr_cnt = 1;
    max_instr_cnt = 3;
  endfunction : new
  
  function void post_randomize();
    super.post_randomize();
    
    instr_list[0].comment = "corev_compressed_load_store_wfi_stream";

    if (first_instr_wfi) begin
      riscv_instr        wfi;

      wfi = riscv_instr::get_rand_instr(.include_instr({WFI}));
      `DV_CHECK_RANDOMIZE_FATAL(wfi);      
      wfi.comment = "Insert first WFI";
      wfi.atomic = 1;
      wfi.label = "0";
      insert_instr(wfi, 1);
    end 

    if (last_instr_wfi) begin
      riscv_instr        wfi;

      wfi = riscv_instr::get_rand_instr(.include_instr({WFI}));
      `DV_CHECK_RANDOMIZE_FATAL(wfi);      
      wfi.comment = "Insert last WFI";
      wfi.atomic = 1;
      wfi.label = "0";
      insert_instr(wfi, instr_list.size());
    end 
    
  endfunction : post_randomize

endclass : corev_compressed_load_store_wfi_stress_instr_stream
