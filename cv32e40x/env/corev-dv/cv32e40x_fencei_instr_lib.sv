// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


// store_fencei_load:
// Run a store, then a fencei, and finally load from the same address as the store.
// Even though fencei meddles with the pipeline, the stores shall come through.
class corev_store_fencei_load_instr_stream extends riscv_load_store_rand_instr_stream;

  rand riscv_reg_t addr_reg;
  rand bit [31:0]  addr;

  `uvm_object_utils(corev_store_fencei_load_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr instr;

    // Store
    instr = riscv_instr::get_rand_instr(.include_instr({SW, SH, SB}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name inside {SW, SH, SB};
      rs1 == addr_reg;
      imm == addr[31:20];
      , "failed to randomize store"
    )
    instr.comment = "store_fencei_load: store";
    instr_list.push_back(instr);

    // Fence.i
    instr = riscv_instr::get_instr(FENCE_I);
    instr.comment = "store_fencei_load: fencei";
    instr_list.push_back(instr);

    // Load
    instr = riscv_instr::get_rand_instr(.include_instr({LW, LH, LHU, LB, LBU}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name inside {LW, LH, LHU, LB, LBU};
      rs1 == addr_reg;
      imm == addr[31:20];
      , "failed to randomize load"
    )
    instr.comment = "store_fencei_load: load";
    instr_list.push_back(instr);

    // Get a nice enumeration label for anything not labeled
    foreach (instr_list[i]) begin
      instr_list[i].atomic = 1;
      if (instr_list[i].label == "") begin
        instr_list[i].label = $sformatf("%0d", i);
      end
    end
  endfunction : post_randomize

endclass : corev_store_fencei_load_instr_stream


// store_fencei_exec:
// The main instructions are [SW, FENCE_I, (random1), (random2)].
// Before that SW is some setup code.
// The SW overwrites the data of random1 with the data from random2.
// Hence, one shall never see random1 execute, but rather 2 consecutive random2.
class corev_store_fencei_exec_instr_stream extends riscv_load_store_rand_instr_stream;

  static int idx_label;

  rand riscv_reg_t addr_reg;
  rand riscv_reg_t data_reg;

  constraint dont_overwrite_data_reg {
    addr_reg != data_reg;  // Don't overwrite the data that is to be written
  }
  constraint dont_pollute_reserved_regs {
    !(addr_reg inside {cfg.reserved_regs});
    !(data_reg inside {cfg.reserved_regs});
  }

  `uvm_object_utils(corev_store_fencei_exec_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr        instr;
    riscv_pseudo_instr pseudo;
    string             label_exec;
    string             label_dummy;

    // Calculate labels with right index
    label_exec = $sformatf("store_fencei_exec__exec_%0d", idx_label);
    label_dummy = $sformatf("store_fencei_exec__dummy_%0d", idx_label);
    idx_label++;

    // Load address of dummy instruction
    pseudo = riscv_pseudo_instr::type_id::create("LA");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LA;
      rd == addr_reg;
      , "failed to randomize LA for dummy instr"
    )
    pseudo.imm_str = label_dummy;
    pseudo.comment = "store_fencei_exec: la dummy";
    instr_list.push_back(pseudo);

    // Load data of dummy instruction
    instr = riscv_instr::get_instr(LW);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == LW;
      rs1 == addr_reg;
      imm == 0;
      rd == data_reg;
      , "failed to randomize LW for dummy instruction"
    )
    instr.comment = "store_fencei_exec: lw dummy";
    instr_list.push_back(instr);

    // Load address of exec instruction
    pseudo = riscv_pseudo_instr::type_id::create("LA");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LA;
      rd == addr_reg;
      , "failed to randomize LA for exec instruction"
    )
    pseudo.imm_str = label_exec;
    pseudo.comment = "store_fencei_exec: la exec";
    instr_list.push_back(pseudo);

    // Store
    instr = riscv_instr::get_instr(SW);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == SW;
      rs1 == addr_reg;
      imm == 0;
      rs2 == data_reg;
      , "failed to randomize store"
    )
    instr.comment = "store_fencei_exec: store";
    instr_list.push_back(instr);

    // Fencei
    instr = riscv_instr::get_instr(FENCE_I);
    instr.comment = "store_fencei_exec: fencei";
    instr_list.push_back(instr);

    // Exec
    instr = riscv_instr::get_rand_instr(.exclude_group({RV32C}));
    `DV_CHECK_RANDOMIZE_FATAL(instr, "failed to randomize exec instruction");
    instr.comment = "store_fencei_exec: exec";
    instr.label = label_exec;
    instr_list.push_back(instr);

    // Dummy, for replacing exec
    instr = riscv_instr::get_rand_instr(.exclude_category({JUMP, BRANCH, SYSTEM}), .exclude_group({RV32C}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      !(category inside {JUMP, BRANCH, SYSTEM});
      // Note: Could allow JUMP/BRANCH, but just not backwards jumps
      , "failed to randomize dummy instruction"
    )
    instr.comment = "store_fencei_exec: dummy";
    instr.label = label_dummy;
    instr_list.push_back(instr);

    // Get a nice enumeration label for anything not labeled
    foreach (instr_list[i]) begin
      instr_list[i].atomic = 1;
      if (instr_list[i].label == "") begin
        instr_list[i].label = $sformatf("%0d", i);
      end
    end
  endfunction : post_randomize

endclass : corev_store_fencei_exec_instr_stream
