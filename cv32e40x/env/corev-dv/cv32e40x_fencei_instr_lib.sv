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
      , "TODO"
    )
    instr.comment = "store_fencei_load: store";
    insert_instr(instr, 0);

    // Fence.i
    instr = riscv_instr::get_instr(FENCE_I);
    instr.comment = "store_fencei_load: fencei";
    insert_instr(instr, 1);

    // Load
    instr = riscv_instr::get_rand_instr(.include_instr({LW, LH, LHU, LB, LBU}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name inside {LW, LH, LHU, LB, LBU};
      rs1 == addr_reg;
      imm == addr[31:20];
      , "TODO"
    )
    instr.comment = "store_fencei_load: load";
    insert_instr(instr, 2);
  endfunction : post_randomize

endclass : corev_store_fencei_load_instr_stream
