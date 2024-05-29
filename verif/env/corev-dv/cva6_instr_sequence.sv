/*
 * Copyright 2018 Google LLC
 * Copyright 2023 Thales DIS

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

//-----------------------------------------------------------------------------------------
// CVA6 instruction sequence, this add unsupported extension instructions to
// hint/illegal instructions
//-----------------------------------------------------------------------------------------

class cva6_instr_sequence_c extends riscv_instr_sequence;

  cva6_instr_gen_config_c       cfg_cva6;                 // Configuration class handle
  cva6_unsupported_instr_c      unsupported_instr;        // unsupported instruction generator
  int                           unsupported_instr_pct;    // Percentage of unsupported instruction

  `uvm_object_utils(cva6_instr_sequence_c)

  function new (string name = "");
    super.new(name);
    unsupported_instr = cva6_unsupported_instr_c::type_id::create("unsupported_instr");
    illegal_instr     = cva6_illegal_instr_c::type_id::create("illegal_instr");
  endfunction

  function void insert_unsupported_instr();
    int bin_instr_cnt;
    int idx;
    string str;
    `DV_CHECK_FATAL($cast(cfg_cva6, cfg), "Could not cast cfg into cfg_cva6")
    bin_instr_cnt = instr_cnt * cfg_cva6.unsupported_instr_ratio / 1000;
    if (bin_instr_cnt >= 0) begin
      `uvm_info(`gfn, $sformatf("Injecting %0d unsupported instructions, ratio %0d/100",
                      bin_instr_cnt, cfg_cva6.unsupported_instr_ratio), UVM_LOW)
      repeat (bin_instr_cnt) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(unsupported_instr, 
                                       unsupported_instr inside {rv64i_instr, rv64c_instr, rv64m_instr, rvfdq_instr, illegal_slli_srai, sys_instr,
                                                                 illegal_rv32zcb_instr, rv64zcb_instr, rv32vf_instr};)
        if (unsupported_instr.compressed) begin
           str = {indent, $sformatf(".2byte 0x%s # %0s",
                          unsupported_instr.get_bin_str(), unsupported_instr.comment)};
                  idx = $urandom_range(0, instr_string_list.size());
           instr_string_list.insert(idx, str);
        end
        else begin
           str = {indent, $sformatf(".4byte 0x%s # %0s",
                          unsupported_instr.get_bin_str(), unsupported_instr.comment)};
                  idx = $urandom_range(0, instr_string_list.size());
           instr_string_list.insert(idx, str);
        end
      end
    end
  endfunction

  function void insert_illegal_hint_instr();
    int bin_instr_cnt;
    int idx;
    string str;
    illegal_instr.init(cfg);
    bin_instr_cnt = instr_cnt * cfg.illegal_instr_ratio / 1000;
    if (bin_instr_cnt >= 0) begin
      `uvm_info(`gfn, $sformatf("Injecting %0d cva6 illegal instructions, ratio %0d/100",
                      bin_instr_cnt, cfg.illegal_instr_ratio), UVM_LOW)
      repeat (bin_instr_cnt) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(illegal_instr,
                                       exception != kHintInstr;)
        str = {indent, $sformatf(".4byte 0x%s # %0s",
                       illegal_instr.get_bin_str(), illegal_instr.comment)};
               idx = $urandom_range(0, instr_string_list.size());
        instr_string_list.insert(idx, str);
      end
    end
    bin_instr_cnt = instr_cnt * cfg.hint_instr_ratio / 1000;
    if (bin_instr_cnt >= 0) begin
      `uvm_info(`gfn, $sformatf("Injecting %0d HINT instructions, ratio %0d/100",
                      bin_instr_cnt, cfg.illegal_instr_ratio), UVM_LOW)
      repeat (bin_instr_cnt) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(illegal_instr,
                                       exception == kHintInstr;)
        str = {indent, $sformatf(".2byte 0x%s # %0s",
                       illegal_instr.get_bin_str(), illegal_instr.comment)};
        idx = $urandom_range(0, instr_string_list.size());
        instr_string_list.insert(idx, str);
      end
    end
  endfunction

  // Convert the instruction stream to the string format.
  // Label is attached to the instruction if available, otherwise attach proper space to make
  // the code indent consistent.
  function void generate_unsupported_instr_stream(bit no_label = 1'b0);
    string prefix, str;
    int i;
    instr_string_list = {};
    for(i = 0; i < instr_stream.instr_list.size(); i++) begin
      if(i == 0) begin
        if (no_label) begin
          prefix = format_string(" ", LABEL_STR_LEN);
        end else begin
          prefix = format_string($sformatf("%0s:", label_name), LABEL_STR_LEN);
        end
        instr_stream.instr_list[i].has_label = 1'b1;
      end else begin
        if(instr_stream.instr_list[i].has_label) begin
          prefix = format_string($sformatf("%0s:", instr_stream.instr_list[i].label),
                   LABEL_STR_LEN);
        end else begin
          prefix = format_string(" ", LABEL_STR_LEN);
        end
      end
      str = {prefix, instr_stream.instr_list[i].convert2asm()};
      instr_string_list.push_back(str);
    end
    insert_unsupported_instr();
    insert_illegal_hint_instr();
    prefix = format_string($sformatf("%0d:", i), LABEL_STR_LEN);
    if(!is_main_program) begin
      generate_return_routine(prefix);
    end
  endfunction

endclass
