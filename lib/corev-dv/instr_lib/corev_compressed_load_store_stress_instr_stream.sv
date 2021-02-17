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
 * corev_compressed_load_store_stress_instr_stream: Extension of riscv_load_store_rand_instr_stream with offsets
 * biased to generate many C_LW and C_SW streams
 */

class corev_compressed_load_store_stress_instr_stream extends riscv_load_store_stress_instr_stream;
  
  constraint sp_c {
    use_sp_as_rs1 dist {1 := 1, 0 := 5};
    if (use_sp_as_rs1) {
      rs1_reg == SP;
    }
  }

  constraint compressed_reg_c {
    rs1_reg inside {[S0:A5], SP};
  }

  `uvm_object_utils(corev_compressed_load_store_stress_instr_stream)
  `uvm_object_new
  
  virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i=0; i<num_load_store; i++) begin
      if (!std::randomize(offset_, addr_) with {
        offset_ inside {[0:127]};     
        offset_[1:0] == 0;
        addr_ == base + offset_;
        addr_ inside {[0 : max_load_store_offset - 1]};
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store offset")
      end
      offset[i] = offset_;
      addr[i] = addr_;
    end
  endfunction : randomize_offset

  function void post_randomize();
    super.post_randomize();

    instr_list[0].comment = "corev_compressed_load_store_stress";
  endfunction : post_randomize

endclass : corev_compressed_load_store_stress_instr_stream

