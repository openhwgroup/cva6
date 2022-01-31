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

  `uvm_object_utils(corev_store_fencei_load_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr instr;
    riscv_instr instr_list_new[$];
    int         idx_insert;

    // Generate a default big chunk of instructions as a "substrate" to work on
    super.post_randomize();

    // The following instrs add to "instr_list_new", to be merged into "instr_list" later

    // Store
    instr = riscv_instr::get_rand_instr(.include_instr({SW, SH, SB}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name inside {SW, SH, SB};
      rs1 == rs1_reg;
      imm == offset[0];
      , "failed to randomize store"
    )
    instr.comment = "store_fencei_load: store";
    instr_list_new.push_back(instr);

    // Fence.i
    instr = riscv_instr::get_instr(FENCE_I);
    instr.comment = "store_fencei_load: fencei";
    instr_list_new.push_back(instr);

    // Load
    instr = riscv_instr::get_rand_instr(.include_instr({LW, LH, LHU, LB, LBU}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name inside {LW, LH, LHU, LB, LBU};
      rs1 == rs1_reg;
      imm == offset[0];
      rd != rs1_reg;
      !(rd inside {cfg.reserved_regs});
      , "failed to randomize load"
    )
    instr.comment = "store_fencei_load: load";
    instr_list_new.push_back(instr);

    // Combine the final instr list
    idx_insert = $urandom_range(1, instr_list.size() - 1);  // Not before the LA
    instr_list = {instr_list[0:idx_insert-1], instr_list_new, instr_list[idx_insert:$]};

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
  constraint dont_store_in_x0 {
    addr_reg != ZERO;
    data_reg != ZERO;
  }

  `uvm_object_utils(corev_store_fencei_exec_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr        instr;
    riscv_pseudo_instr pseudo;
    corev_directive_instr directive;
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

    // Add norvc/rvc guards around the instr after fencei
    directive = corev_directive_instr::type_id::create("corev_directive_instr");
    directive.directive = ".option push";
    instr_list.push_back(directive);
    directive = corev_directive_instr::type_id::create("corev_directive_instr");
    directive.directive = ".option norvc";
    instr_list.push_back(directive);

    // Exec
    instr = riscv_instr::get_rand_instr(.exclude_instr({NOP}), .exclude_group({RV32C}));
    instr.imm.rand_mode(0);
    `DV_CHECK_RANDOMIZE_FATAL(instr, "failed to randomize exec instruction"
    )
    case (instr.instr_name)
      JAL: begin
        instr.imm_str = "1b";
      end
      BEQ, BNE, BLT, BGE, BLTU, BGEU: begin
        instr.imm_str = "1b";
        instr.branch_assigned = 1'b1;
      end
    endcase
    instr.comment = "store_fencei_exec: exec";
    instr.label = label_exec;
    instr_list.push_back(instr);

    // Dummy, for replacing exec
    instr = riscv_instr::get_rand_instr(
      .include_category({LOAD, SHIFT, ARITHMETIC, LOGICAL, COMPARE, SYNCH}),
      .exclude_group({RV32C}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      (category inside {LOAD, SHIFT, ARITHMETIC, LOGICAL, COMPARE, SYNCH});
        // Note: Several of the constraints could be relaxed, but it turns really complicated
      !(rd inside {cfg.reserved_regs});
      !((rd == ZERO) && (instr_name inside {ADDI, C_ADDI}));
      , "failed to randomize dummy instruction"
    )

    // restore compiler options
    instr.comment = "store_fencei_exec: dummy";
    instr.label = label_dummy;
    instr_list.push_back(instr);

    directive = corev_directive_instr::type_id::create("corev_directive_instr");
    directive.directive = ".option pop";
    instr_list.push_back(directive);

    // Get a nice enumeration label for anything not labeled
    foreach (instr_list[i]) begin
      instr_list[i].atomic = 1;
      if (instr_list[i].label == "") begin
        instr_list[i].label = $sformatf("%0d", i);
      end
    end
  endfunction : post_randomize

endclass : corev_store_fencei_exec_instr_stream


// vp_fencei_exec:
// 1) Configures and enables the fencei-triggered memory-changing vp (instr_list_pre).
// 2) Runs a bunch of random instruction with a fence.i somewhere in between (instr_list).
// 3) (Lets vp do its thing).
// 4) Disables vp (instr_list_post).
class corev_vp_fencei_exec_instr_stream extends riscv_load_store_rand_instr_stream;

  static int       idx_label;
  rand riscv_reg_t vp_reg;
  rand riscv_reg_t tmp_reg;
  riscv_instr      instr_list_pre[$];
  riscv_instr      instr_list_post[$];

  localparam CV_VP_REGISTER_BASE = 32'h 00800000;
  localparam CV_VP_FENCEI_TAMPER_OFFSET = 32'h 00000100;
  localparam CV_VP_FENCEI_TAMPER_BASE = (CV_VP_REGISTER_BASE + CV_VP_FENCEI_TAMPER_OFFSET);
  // Note: Would preferably be from uvme_cv32e40x_pkg, which is seemingly not easily available in core-v compilation

  constraint dont_overwrite_regs {
    vp_reg != tmp_reg;  // Don't overwrite the data that is to be written
  }
  constraint dont_pollute_reserved_regs {
    !(vp_reg inside {cfg.reserved_regs, reserved_rd});
    !(tmp_reg inside {cfg.reserved_regs, reserved_rd});
  }
  constraint dont_store_in_x0 {
    vp_reg != ZERO;
    tmp_reg != ZERO;
  }

  `uvm_object_utils(corev_vp_fencei_exec_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr           instr;
    riscv_pseudo_instr    pseudo;
    corev_directive_instr directive;
    string                label_fencei;
    string                label_dummy;
    int                   idx_fencei;

    // Calculate labels with right index
    label_fencei = $sformatf("vp_fencei_exec__fencei_%0d", idx_label);
    label_dummy = $sformatf("vp_fencei_exec__dummy_%0d", idx_label);
    idx_label++;


    // Generate the random code to be executed

    // Generate a default big chunk of instructions as a "substrate" to work on
    super.post_randomize();

    // Add a fence.i to a random location, and label it
    instr = riscv_instr::get_instr(FENCE_I);
    instr.comment = "vp_fencei_exec: fencei";
    instr.label = label_fencei;
    idx_fencei = $urandom_range(0, instr_list.size() - 1);
    while(!is_ok_target(instr_list[idx_fencei])) begin
      idx_fencei++;
      if (idx_fencei == instr_list.size()) begin
        idx_fencei = 0;
      end
    end
    instr_list.insert(idx_fencei, instr);
    // Add norvc/rvc guards around the instr after fencei
    directive = corev_directive_instr::type_id::create("corev_directive_instr");
    directive.directive = ".option norvc";
    instr_list.insert(idx_fencei + 1, directive);
    directive = corev_directive_instr::type_id::create("corev_directive_instr");
    directive.directive = ".option rvc";
    instr_list.insert(idx_fencei + 3, directive);

    // Add a dummy instr at the top
    instr = riscv_instr::get_rand_instr(
      .exclude_instr({NOP}),
      .include_category({LOAD, SHIFT, ARITHMETIC, LOGICAL, COMPARE, SYNCH}),
      .exclude_group({RV32C}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      (category inside {LOAD, SHIFT, ARITHMETIC, LOGICAL, COMPARE, SYNCH});
        // Note: Several of the constraints could be relaxed, but it turns really complicated
      !(rd inside {cfg.reserved_regs, reserved_rd});
      !((rd == ZERO) && (instr_name inside {ADDI, C_ADDI}));
      instr_name != NOP;
      , "failed to randomize dummy instruction"
    )
    instr.comment = "vp_fencei_exec: dummy";
    instr.label = label_dummy;
    // Add rvc  (nb, reverse order, 3/3)
    directive = corev_directive_instr::type_id::create("corev_directive_instr");
    directive.directive = ".option rvc";
    instr_list.push_front(directive);
    // Add instr  (nb, reverse order, 2/3)
    instr_list.push_front(instr);
    // Add norvc  (nb, reverse order, 1/3)
    directive = corev_directive_instr::type_id::create("corev_directive_instr");
    directive.directive = ".option norvc";
    instr_list.push_front(directive);


    // Configure the vp addr register

    // Load addr of fencei
    pseudo = riscv_pseudo_instr::type_id::create("LA");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LA;
      rd == tmp_reg;
      , "failed to randomize LA"
    )
    pseudo.imm_str = label_fencei;
    pseudo.comment = "vp_fencei_exec: la fencei";
    instr_list_pre.push_back(pseudo);

    // Add 4 to get the addr of the instr following fencei
    instr = riscv_instr::get_instr(ADDI);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == ADDI;
      rs1 == tmp_reg;
      rd == tmp_reg;
      imm == 4;
      , "failed to randomize addi 4"
    )
    instr.comment = "vp_fencei_exec: +4";
    instr_list_pre.push_back(instr);

    // Load the addr of the vp's register base
    pseudo = riscv_pseudo_instr::type_id::create("LI");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LI;
      rd == vp_reg;
      , "failed to randomize LI"
    )
    pseudo.imm_str = $sformatf("0x%08x", CV_VP_FENCEI_TAMPER_BASE);
    pseudo.comment = "vp_fencei_exec: LI vp addr reg addr";
    instr_list_pre.push_back(pseudo);

    // Store the addr in the vp's addr register
    instr = riscv_instr::get_instr(SW);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == SW;
      rs1 == vp_reg;  // addr of mem to put in
      rs2 == tmp_reg;  // data to put in mem
      imm == 4;  // 4, to access reg 1 of vp, namely "addr"
      , "failed to randomize SW"
    )
    instr.comment = "vp_fencei_exec: fencei+4 -> vpaddr";
    instr_list_pre.push_back(instr);


    // Configure the vp data register

    // Load address of dummy instruction
    pseudo = riscv_pseudo_instr::type_id::create("LA");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LA;
      rd == tmp_reg;
      , "failed to randomize LA, dummy"
    )
    pseudo.imm_str = label_dummy;
    pseudo.comment = "vp_fencei_exec: la dummy";
    instr_list_pre.push_back(pseudo);

    // Load data of dummy instruction
    instr = riscv_instr::get_instr(LW);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == LW;
      rs1 == tmp_reg;
      imm == 0;
      rd == tmp_reg;
      , "failed to randomize LW for dummy instruction"
    )
    instr.comment = "vp_fencei_exec: lw dummy";
    instr_list_pre.push_back(instr);

    // Load the addr of the vp's register base
    pseudo = riscv_pseudo_instr::type_id::create("LI");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LI;
      rd == vp_reg;
      , "failed to randomize LI, data"
    )
    pseudo.imm_str = $sformatf("0x%08x", CV_VP_FENCEI_TAMPER_BASE);
    pseudo.comment = "vp_fencei_exec: LI vp reg base";
    instr_list_pre.push_back(pseudo);

    // Store the data in the vp's data register
    instr = riscv_instr::get_instr(SW);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == SW;
      rs1 == vp_reg;  // addr of mem to put in
      rs2 == tmp_reg;  // data to put in mem
      imm == 8;  // 8, to access reg 2 of vp, namely "data"
      , "failed to randomize SW"
    )
    instr.comment = "vp_fencei_exec: dummy -> vpdata";
    instr_list_pre.push_back(instr);


    // Enable vp before running the random instructions

    // Load immediate 1
    pseudo = riscv_pseudo_instr::type_id::create("LI");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LI;
      rd == tmp_reg;
      , "failed to randomize LI, 1"
    )
    pseudo.imm_str = "1";
    pseudo.comment = "vp_fencei_exec: LI 1";
    instr_list_pre.push_back(pseudo);

    // Load the addr of the vp's register base
    pseudo = riscv_pseudo_instr::type_id::create("LI");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LI;
      rd == vp_reg;
      , "failed to randomize LI, enab"
    )
    pseudo.imm_str = $sformatf("0x%08x", CV_VP_FENCEI_TAMPER_BASE);
    pseudo.comment = "vp_fencei_exec: LI vp reg base";
    instr_list_pre.push_back(pseudo);

    // Store the 1 in the vp's enabled register
    instr = riscv_instr::get_instr(SW);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == SW;
      rs1 == vp_reg;  // addr of mem to put in
      rs2 == tmp_reg;  // data to put in mem
      imm == 0;  // 0, to access reg 0 of vp, namely "enabled"
      , "failed to randomize SW"
    )
    instr.comment = "vp_fencei_exec: enabled";
    instr_list_pre.push_back(instr);


    // Disable vp when done

    // Load the addr of the vp's register base
    pseudo = riscv_pseudo_instr::type_id::create("LI");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pseudo,
      pseudo_instr_name == LI;
      rd == vp_reg;
      , "failed to randomize LI, disab"
    )
    pseudo.imm_str = $sformatf("0x%08x", CV_VP_FENCEI_TAMPER_BASE);
    pseudo.comment = "vp_fencei_exec: LI vp reg base";
    instr_list_post.push_back(pseudo);

    // Store a 0 in the vp's enabled register
    instr = riscv_instr::get_instr(SW);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == SW;
      rs1 == vp_reg;  // addr of mem to put in
      rs2 == ZERO;  // data to put in mem
      imm == 0;  // 0, to access reg 0 of vp, namely "enabled"
      , "failed to randomize SW"
    )
    instr.comment = "vp_fencei_exec: disabled";
    instr_list_post.push_back(instr);


    // Combine the final instr list

    instr_list = {instr_list_pre, instr_list, instr_list_post};


    // Get a nice enumeration label for anything not labeled

    foreach (instr_list[i]) begin
      instr_list[i].atomic = 1;
      if (instr_list[i].label == "") begin
        instr_list[i].label = $sformatf("%0d", i);
      end
    end
  endfunction : post_randomize

  function logic is_ok_target(riscv_instr instr);
    // Note: Could allow 16bit instrs, but that requires more accommodations
    return (
      (instr.group != RV32C)
      && (instr.instr_name != NOP)
      && !((instr.rd == ZERO) && (instr.instr_name inside {ADDI, C_ADDI}))
      && !(instr.rd inside {cfg.reserved_regs, reserved_rd})
      );
  endfunction : is_ok_target

endclass : corev_vp_fencei_exec_instr_stream
