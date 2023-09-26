/*
 * Copyright 2018 Google LLC
 * Copyright 2023 Thales DIS
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

// class for hazard instruction stream (RAW)
// that means destination register of previous instruction is the same source register of the current instruction 

class cva6_reg_hazard_stream_c extends riscv_rand_instr_stream;

  `uvm_object_utils(cva6_reg_hazard_stream_c)

  string label;

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void gen_instr(bit no_branch = 1'b0, bit no_load_store = 1'b1,
                                  bit is_debug_program = 1'b0);
    riscv_reg_t prev_reg;
    cva6_instr_gen_config_c cfg_cva6;
    `DV_CHECK_FATAL($cast(cfg_cva6, cfg), "Could not cast cfg into cfg_cva6")
    setup_allowed_instr(no_branch, no_load_store);
    foreach(instr_list[i]) begin
      if (i == 0) begin
        randomize_instr(instr_list[i], is_debug_program);
        prev_reg = instr_list[i].rd;
      end
      else if (i >= 1) begin
        randomize_instr(instr_list[i], is_debug_program);
         if (!instr_list[i].is_compressed) begin
           `DV_CHECK_RANDOMIZE_WITH_FATAL(instr_list[i],
              if (has_rs1 && cfg_cva6.enable_rdrs1_hazard) {
                instr_list[i].rs1 == prev_reg;
                }
              if (has_rs2 && cfg_cva6.enable_rdrs2_hazard) {
                instr_list[i].rs2 == prev_reg;
                }
              if (cfg_cva6.enable_same_reg) {
                instr_list[i].rd == instr_list[i].rs1;
                instr_list[i].rs1 == instr_list[i].rs2;
                })
            prev_reg = instr_list[i].rd;
          end
         else begin
           `DV_CHECK_RANDOMIZE_WITH_FATAL(instr_list[i],
              if (instr_list[i-1].rd inside {[S0:A5]}) {
                 if (has_rs1 && cfg_cva6.enable_rdrs1_hazard) {
                   instr_list[i].rs1 == prev_reg;
                 }
                 if (has_rs2 && cfg_cva6.enable_rdrs2_hazard) {
                   instr_list[i].rs2 == prev_reg;
                 }})
              prev_reg = instr_list[i].rd;
          end
     end
    end
    // Do not allow branch instruction as the last instruction because there's no
    // forward branch target
    while (instr_list[$].category == BRANCH) begin
      void'(instr_list.pop_back());
      if (instr_list.size() == 0) break;
    end
  endfunction

endclass
