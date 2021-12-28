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


// #############################################################################
//
// Section 1: Load/Store test streams
//
// #############################################################################

// -----------------------------------------------------------------------------
//
// corev_load_store_pma_base_stream
//
// Directed test to generate random load instruction to random pma_region
// -----------------------------------------------------------------------------
virtual class corev_load_store_pma_base_stream extends riscv_load_store_rand_instr_stream;
  cv32e40x_pma_cfg pma_cfg;
  rand int unsigned load_cnt;
  rand int unsigned store_cnt;
  rand riscv_reg_t protected_reg[];
  rand riscv_reg_t addr_reg;
  rand bit [31:0] addr;
  rand bit use_compressed;
  rand int index;
  rand bit region_access_only;
  rand bit non_region_access_only;

  constraint valid_addr_reg_c {
    use_compressed -> (addr_reg inside {[S0:A5]});
    !use_compressed -> (addr_reg inside {[T0:T6]});
  }

  constraint valid_index_c {
    index inside {[0 : pma_cfg.pma_num_regions - 1]};
  }

  constraint non_region_access_only_c {
    non_region_access_only == 1 -> region_access_only == 0;
  }

  constraint only_valid_region_c {
    region_access_only == 1;
    non_region_access_only == 0;
  }

  constraint valid_region_c {
    if (region_access_only == 1) {
      addr inside {[pma_cfg.regions[index].word_addr_low<<2:pma_cfg.regions[index].word_addr_high<<2]};
    }
    if (non_region_access_only == 1) {
      foreach (pma_cfg.regions[i]) {
        !(addr inside {[pma_cfg.regions[i].word_addr_low<<2:pma_cfg.regions[i].word_addr_high<<2]});
      }
    }
  }

  constraint load_cnt_c {
    load_cnt inside { [ 3:10 ] };
    store_cnt inside { [ 3:10 ] };
  }

  function new(string name = "");
    super.new(name);
    pma_cfg = cv32e40x_pma_cfg::type_id::create("pma_cfg");
  endfunction : new


endclass : corev_load_store_pma_base_stream

// -----------------------------------------------------------------------------
//
// corev_load_pma_instr_stream
//
// FIXME silabs-hfegran: This stream appears to generate an extra load store sequence
// -----------------------------------------------------------------------------
class corev_load_pma_instr_stream extends corev_load_store_pma_base_stream;
  rand riscv_reg_t dest_reg;

  constraint valid_rd_c {
    use_compressed -> (dest_reg inside {[S0:A5]});
    !use_compressed -> (dest_reg inside {[T0:T6]});
    dest_reg != addr_reg;
  }

  `uvm_object_utils(corev_load_pma_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual function void add_mixed_instr(int instr_cnt);
    riscv_reg_t all_regs;
    riscv_reg_t nonprotected_regs[$];

    do begin
      if ((all_regs.name != addr_reg.name) && (all_regs >= T0)) begin
        nonprotected_regs.push_back(all_regs);
      end
      all_regs = all_regs.next;
    end while (all_regs != all_regs.first);
    super.avail_regs = nonprotected_regs;

    add_pma_load(load_cnt);
    super.add_mixed_instr(instr_cnt);
  endfunction : add_mixed_instr

  virtual function void add_pma_load(int unsigned cnt);
    riscv_instr instr;

    instr = riscv_instr::get_rand_instr(.include_instr({LUI}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == LUI;
      rd == addr_reg;
      imm == addr[31:12];
      , "Failed randomizing LUI"
    )
    instr.comment = $sformatf("start corev_load_pma_instr (imm: %0x, region: %0d)", instr.imm, index);
    insert_instr(instr, 0);

    for (int i = 1; i <= cnt; i++) begin
      instr = riscv_instr::get_rand_instr(.include_instr({LB, LH, LW, LBU, LHU}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        instr_name inside { LB, LH, LW, LBU, LHU };
        rd == dest_reg;
        rs1 == addr_reg;
        if (region_access_only == 1) {
          (addr + imm) inside { [ pma_cfg.regions[index].word_addr_low<<2:pma_cfg.regions[index].word_addr_high<<2 ] }
        };
        , $sformatf("Failed randomizing %0s", instr.instr_name)
      )
      instr.comment = $sformatf("corev-dv: corev_load_pma_instr_stream: addr: %0x, imm: %0x", this.addr, instr.imm);
      insert_instr(instr, i);
    end
  endfunction : add_pma_load

  function void post_randomize();
    // Cannot call super.randomize() because the parent class will add more instructions
    // that can corrupt this stream, this is a replication of the base class post_randomze()
    // This needs a better solution, file Issue on this
    add_mixed_instr(num_mixed_instr);

    foreach(instr_list[i]) begin
      instr_list[i].has_label = 1'b0;
      instr_list[i].atomic = 1'b1;
    end
    instr_list[0].comment = $sformatf("Start %0s", get_name());
    instr_list[$].comment = $sformatf("End %0s", get_name());
    if(label!= "") begin
      instr_list[0].label = label;
      instr_list[0].has_label = 1'b1;
    end

  endfunction : post_randomize

endclass : corev_load_pma_instr_stream

// -----------------------------------------------------------------------------
//
// corev_store_pma_instr_stream
//
// Multiple writes to same address range
//
// -----------------------------------------------------------------------------
class corev_store_pma_instr_stream extends corev_load_store_pma_base_stream;

  `uvm_object_utils(corev_store_pma_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual function void add_mixed_instr(int instr_cnt);
    riscv_reg_t all_regs;
    riscv_reg_t nonprotected_regs[$];

    do begin
      if ((all_regs.name != addr_reg.name) && (all_regs >= T0)) begin
        nonprotected_regs.push_back(all_regs);
      end
      all_regs = all_regs.next;
    end while (all_regs != all_regs.first);
    super.avail_regs = nonprotected_regs;

    add_pma_store(store_cnt);
    super.add_mixed_instr(instr_cnt);
  endfunction : add_mixed_instr

  virtual function void add_pma_store(int unsigned cnt);
    riscv_instr instr;
    instr = riscv_instr::get_rand_instr(.include_instr({LUI}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == LUI;
      rd == addr_reg;
      imm == addr[31:12];
      , "Failed randomizing LUI"
    )
    instr.comment = $sformatf("start corev_store_pma_instr (Reg: %0s, Imm: %0x)", instr.rd.name, instr.imm);
    insert_instr(instr, 0);

    for (int i = 1; i <= cnt; i++) begin
      instr = riscv_instr::get_rand_instr(.include_instr({SB, SH, SW}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        instr_name inside {SB, SH, SW};
        rs1 == addr_reg;
        (addr + imm) inside { [pma_cfg.regions[index].word_addr_low<<2:pma_cfg.regions[index].word_addr_high<<2 ] };
        , $sformatf("Failed randomizing %0s", instr.instr_name)
      )
      instr.comment = $sformatf("corev-dv: corev_store_pma_instr_stream: addr: %0x, imm: %0x", this.addr, instr.imm);
      insert_instr(instr, i);
    end
  endfunction : add_pma_store

endclass : corev_store_pma_instr_stream

// -----------------------------------------------------------------------------
//
// corev_load_store_pma_mixed_instr_stream
//
// Mixed reads and writes from same address range
//
// -----------------------------------------------------------------------------
class corev_load_store_pma_mixed_instr_stream extends corev_load_store_pma_base_stream;

  rand riscv_reg_t dest_reg;
  rand int cnt;

  constraint valid_cnt_c {
    cnt inside {[5:30]};
  }

  constraint valid_rd_c {
    use_compressed -> (dest_reg inside {[S0:A5]});
    !use_compressed -> (dest_reg inside {[T0:T6]});
    dest_reg != addr_reg;
  }

  `uvm_object_utils(corev_load_store_pma_mixed_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual function void add_mixed_instr(int instr_cnt);
    riscv_reg_t all_regs;
    riscv_reg_t nonprotected_regs[$];

    do begin
      if ((all_regs.name != addr_reg.name) && (all_regs >= T0)) begin
        nonprotected_regs.push_back(all_regs);
      end
      all_regs = all_regs.next;
    end while (all_regs != all_regs.first);
    super.avail_regs = nonprotected_regs;

    super.add_mixed_instr(instr_cnt);

  endfunction : add_mixed_instr

  virtual function void add_pma_load_store_mixed(int unsigned cnt);
    riscv_instr instr;
    instr = riscv_instr::get_rand_instr(.include_instr({LUI}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == LUI;
      rd == addr_reg;
      imm == addr[31:12];
      , "Failed randomizing LUI"
    )
    instr.comment = $sformatf("start corev_load_store_pma_mixed_instr_stream");
    insert_instr(instr, 0);

    for (int i = 1; i <= cnt; i++) begin
      instr = riscv_instr::get_rand_instr(.include_instr({ SB, SH, SW, LB, LH, LW, LBU, LHU }));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        instr_name inside { SB, SH, SW,  LB, LH, LW, LBU, LHU };
        instr_name inside { LB, LH, LW, LBU, LHU } -> rd == dest_reg;
        rs1 == addr_reg;
        if (region_access_only) {
          (addr + imm) inside { [pma_cfg.regions[index].word_addr_low<<2:pma_cfg.regions[index].word_addr_high<<2] };
        }
        , $sformatf("Failed randomizing %0s", instr.instr_name)
      )
      instr.comment = $sformatf("corev-dv: corev_load_store_pma_mixed_instr_stream: addr: %0x, imm: %0x", this.addr, instr.imm);;
      insert_instr(instr, i);
    end
  endfunction : add_pma_load_store_mixed


  function void post_randomize();
    // Cannot call super.randomize() because the parent class will add more instructions
    // that can corrupt this stream, this is a replication of the base class post_randomze()
    // This needs a better solution, file Issue on this

    randomize_offset();
    // rs1 cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) begin
      reserved_rd = {reserved_rd, rs1_reg};
    end
    add_pma_load_store_mixed(cnt);
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);

    foreach(instr_list[i]) begin
      instr_list[i].has_label = 1'b0;
      instr_list[i].atomic = 1'b1;
    end
    instr_list[0].comment = $sformatf("Start %0s", get_name());
    instr_list[$].comment = $sformatf("End %0s", get_name());
    if(label!= "") begin
      instr_list[0].label = label;
      instr_list[0].has_label = 1'b1;
    end

  endfunction

endclass : corev_load_store_pma_mixed_instr_stream

// -----------------------------------------------------------------------------
//
// corev_load_store_pma_misaligned_instr_stream
//
// -----------------------------------------------------------------------------
class corev_load_store_pma_misaligned_instr_stream extends corev_load_store_pma_mixed_instr_stream;

  `uvm_object_utils(corev_load_store_pma_misaligned_instr_stream)

  constraint only_valid_region_c {
  }

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual function void add_pma_load_store_mixed(int unsigned cnt);
    riscv_instr instr;
    instr = riscv_instr::get_rand_instr(.include_instr({LUI}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == LUI;
      rd == addr_reg;
      imm == addr[31:12];
      , "Failed randomizing LUI"
    )
    instr.comment = $sformatf("start %m");
    insert_instr(instr, 0);

    for (int i = 1; i <= cnt; i++) begin
      instr = riscv_instr::get_rand_instr(.include_instr({ SH, SW, LH, LW, LHU }));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        instr_name inside { SH, SW, LH, LW, LHU };
        instr_name inside { LH, LW, LHU } -> rd == dest_reg;
        rs1 == addr_reg;
        if (region_access_only) {
          (addr + imm) inside { [pma_cfg.regions[index].word_addr_low<<2:pma_cfg.regions[index].word_addr_high<<2] }
        };
        (addr + imm % 4) != 0;
        , $sformatf("Failed randomizing %0s", instr.instr_name)
      )
      instr.comment = $sformatf("corev-dv: corev_load_store_pma_misaligned_instr_stream: addr: %0x, imm: %0x", this.addr, instr.imm);;
      insert_instr(instr, i);
    end
  endfunction : add_pma_load_store_mixed

  function void post_randomize();
    // Cannot call super.randomize() because the parent class will add more instructions
    // that can corrupt this stream, this is a replication of the base class post_randomze()
    // This needs a better solution, file Issue on this

    randomize_offset();
    // rs1 cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) begin
      reserved_rd = {reserved_rd, rs1_reg};
    end
    add_pma_load_store_mixed(cnt);
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);

    foreach(instr_list[i]) begin
      instr_list[i].has_label = 1'b0;
      instr_list[i].atomic = 1'b1;
    end
    instr_list[0].comment = $sformatf("Start %0s", get_name());
    instr_list[$].comment = $sformatf("End %0s", get_name());
    if(label!= "") begin
      instr_list[0].label = label;
      instr_list[0].has_label = 1'b1;
    end
  endfunction

endclass : corev_load_store_pma_misaligned_instr_stream

// #############################################################################
//
// Section 2: Jump/Branch test streams
//
// #############################################################################

// -----------------------------------------------------------------------------
//
// corev_jalr_pma_instr
//
// Jump to random address in random defined memory region
//
// -----------------------------------------------------------------------------
class corev_jalr_pma_instr extends riscv_jal_instr;
  cv32e40x_pma_cfg pma_cfg;
  rand riscv_reg_t fwd_addr_reg;
  rand bit use_compressed;
  rand bit [31:0] fwd_addr;
  rand int index;
  static int jmp_label_idx;
  string jmp_label;

  int ram_region;

  constraint valid_reg_c {
    !(fwd_addr_reg inside {cfg.reserved_regs});
    fwd_addr_reg != cfg.gpr[2];
    fwd_addr_reg != cfg.gpr[3];
    fwd_addr_reg != cfg.sp;
    fwd_addr_reg != cfg.tp;
    // Always use compressed instruction targetable register
    use_compressed -> (fwd_addr_reg inside {[S0:A5]});
    !use_compressed -> (fwd_addr_reg inside {[T0:T6]});
  }

  // Don't jump to addresses with executable code (potential infinite loop problems)
  constraint valid_index_c {
    index inside {[0 : pma_cfg.pma_num_regions - 1]};
    index != ram_region;
  }

  constraint valid_region_c {
    fwd_addr inside {[(pma_cfg.regions[index].word_addr_low)<<2:pma_cfg.regions[index].word_addr_high<<2]};

  }

  constraint fwd_addr_max_c {
    // OVPSim cannot fetch instructions at end of its memory
    fwd_addr <= 32'hffff_fff0;
  }

  constraint instr_c {
    num_of_jump_instr == 0;
  }

  `uvm_object_utils(corev_jalr_pma_instr)

  function new(string name = "");
    super.new(name);
    pma_cfg = cv32e40x_pma_cfg::type_id::create("pma_cfg");
    // find region containing RAM
    foreach (pma_cfg.regions[i]) begin
      if (pma_cfg.regions[i].main == 1) begin
        ram_region = i;
        break;
      end
    end
  endfunction : new

  virtual function void add_load_pma_main_addr_instr();
    riscv_instr instr;
    riscv_pseudo_instr la_instr;
    riscv_instr_name_t store_instr = (XLEN == 32) ? SW : SD;
    riscv_instr_name_t load_instr = (XLEN == 32) ? LW : LD;
    automatic bit [11:0] fwd_addr_modif = { fwd_addr[11], 13'h1000 + signed'(fwd_addr[11:0]) };

    // Create recovery mechanism for invalid instruction
    // at destination, we need to be able to resusme
    // execution at jump origin after potential traps

    // Make space on stack for signatures and backup
    instr = riscv_instr::get_rand_instr(.include_instr({ADDI}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == ADDI;
      rd == cfg.sp;
      rs1 == cfg.sp;
      imm == -4*(XLEN/8);
      , "Failed randomizing ADDI"
    )
    insert_instr(instr, 0);

    // Save Original T3 and T4 on stack
    instr = riscv_instr::get_rand_instr(.include_instr({store_instr}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == store_instr;
      rs1 == cfg.sp;
      rs2 == cfg.gpr[2];
      imm == 3*(XLEN/8);
      , {"Failed randomizing ", store_instr.name }
    )
    insert_instr(instr, 1);

    instr = riscv_instr::get_rand_instr(.include_instr({store_instr}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == store_instr;
      rs1 == cfg.sp;
      rs2 == cfg.gpr[3];
      imm == 2*(XLEN/8);
      , {"Failed randomizing ", store_instr.name }
    )
    insert_instr(instr, 2);

    jmp_label = $sformatf("jmp_mret_loc_%0d", jmp_label_idx++);
    // Store future PC (at JALR instrution)
    la_instr = riscv_pseudo_instr::type_id::create("LA");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(la_instr,
      pseudo_instr_name == LA;
      rd == cfg.gpr[2];
      , "Failed randomizing LA"
    )
    la_instr.imm_str = jmp_label;
    la_instr.comment = $sformatf("STORE FUTURE PC T3");
    insert_instr(la_instr, 3);

    // Store future PC (at JALR instrution)
    instr = riscv_instr::get_rand_instr(.include_instr({ADDI}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == ADDI;
      rd == cfg.gpr[3];
      rs1 == cfg.gpr[2];
      imm == 0;
      , "Failed randomizing ADDI"
    )
    instr.comment = $sformatf("STORE FUTURE PC T4");
    insert_instr(instr, 4);

    // Save values on stack
    instr = riscv_instr::get_rand_instr(.include_instr({store_instr}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == store_instr;
      rs2 == cfg.gpr[2];
      rs1 == cfg.sp;
      imm == 0*(XLEN/8);
      , {"Failed randomizing ", store_instr.name }
    )
    insert_instr(instr, 5);

    instr = riscv_instr::get_rand_instr(.include_instr({store_instr}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == store_instr;
      rs2 == cfg.gpr[3];
      rs1 == cfg.sp;
      imm == 1*(XLEN/8);
      , {"Failed randomizing ", store_instr.name }
    )
    insert_instr(instr, 6);

    // Prepare jump
    instr = riscv_instr::get_rand_instr(.include_instr({LUI}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == LUI;
      rd == fwd_addr_reg;
      fwd_addr[11] -> imm == (fwd_addr[31:12] + 1);
      !fwd_addr[11] -> imm == fwd_addr[31:12];
      , "Failed randomizing LUI"
    )
    instr.comment = $sformatf("start corev_jalr_pma_instr (imm: %0x, region: %0d)", instr.imm, index);
    insert_instr(instr, 7);

    instr = riscv_instr::get_rand_instr(.include_instr({JALR}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == JALR;
      rs1 == fwd_addr_reg;
      // don't overwrite protected regs
      rd != cfg.sp;
      rd != cfg.tp;
      rd != cfg.gpr[2];
      rd != cfg.gpr[3];
      fwd_addr[11] -> imm == fwd_addr_modif;
      !fwd_addr[11] -> imm == fwd_addr[11:0];
      , "Failed randomizing JALR"
    )
    insert_instr(instr, 8);

    // Restore t4 and t3
    instr = riscv_instr::get_rand_instr(.include_instr({load_instr}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == load_instr;
      rd == cfg.gpr[3];
      rs1 == cfg.sp;
      imm == 2*(XLEN/8);
      , "Failed randomizing ADDI"
    )
    instr.atomic = 1;
    instr.label = jmp_label;
    insert_instr(instr, 9);

    instr = riscv_instr::get_rand_instr(.include_instr({load_instr}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == load_instr;
      rd == cfg.gpr[2];
      rs1 == cfg.sp;
      imm == 3*(XLEN/8);
      , "Failed randomizing ADDI"
    )
    insert_instr(instr, 10);

    // Cleanup stack
    instr = riscv_instr::get_rand_instr(.include_instr({ADDI}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == ADDI;
      rd == cfg.sp;
      rs1 == cfg.sp;
      imm == 4*(XLEN/8);
      , "Failed randomizing ADDI"
    )
    insert_instr(instr, 11);

  endfunction : add_load_pma_main_addr_instr

  function void post_randomize();
    reserved_rd = { reserved_rd, cfg.gpr[2], cfg.gpr[3], cfg.tp, cfg.sp };
    add_load_pma_main_addr_instr();
    foreach (instr_list[i]) begin
      instr_list[i].atomic = 1;
      if (instr_list[i].label == "") begin
        instr_list[i].label = $sformatf("%0d", i);
      end
    end
  endfunction : post_randomize
endclass : corev_jalr_pma_instr

// -----------------------------------------------------------------------------
//
// corev_jalr_pma_cacheable_instr
//
// Absolute jump to pma-region defined as cacheable
//
// -----------------------------------------------------------------------------
class corev_jalr_pma_cacheable_instr extends corev_jalr_pma_instr;
  constraint valid_index_in_cacheable_region_c {
    pma_cfg.regions[index].cacheable == 1'b1;
  }

  `uvm_object_utils(corev_jalr_pma_cacheable_instr)
  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    super.post_randomize();
    for (int i = 0; i < 2; i++) begin
      if (instr_list[i].instr_name == LUI) begin
        instr_list[i].comment = $sformatf("corev_jalr_pma_cacheable_instr: region: %0d", index);
      end
    end
  endfunction : post_randomize
endclass : corev_jalr_pma_cacheable_instr

// -----------------------------------------------------------------------------
//
// corev_jalr_pma_bufferable_instr
//
// Absolute jump to pma-region defined as bufferable
//
// -----------------------------------------------------------------------------
class corev_jalr_pma_bufferable_instr extends corev_jalr_pma_instr;
  constraint valid_index_in_bufferable_region_c {
    pma_cfg.regions[index].bufferable == 1'b1;
  }

  `uvm_object_utils(corev_jalr_pma_bufferable_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    super.post_randomize();
    for (int i = 0; i < 2; i++) begin
      if (instr_list[i].instr_name == LUI) begin
        instr_list[i].comment = $sformatf("corev_jalr_pma_bufferable_instr: region: %0d", index);
      end
    end
  endfunction : post_randomize
endclass : corev_jalr_pma_bufferable_instr

// -----------------------------------------------------------------------------
//
// corev_jalr_pma_undefined_region_instr
//
// Absolute jump to memory area not covered by any pma-region
//
// -----------------------------------------------------------------------------
class corev_jalr_pma_undefined_region_instr extends corev_jalr_pma_instr;

  constraint valid_region_c {
    foreach (pma_cfg.regions[i]) {
      !(fwd_addr inside {[pma_cfg.regions[i].word_addr_low<<2:pma_cfg.regions[i].word_addr_high<<2]});
    }
  }

  `uvm_object_utils(corev_jalr_pma_undefined_region_instr)

  function new(string name ="");
    super.new(name);
  endfunction : new

  function void post_randomize();
    super.post_randomize();
    for (int i = 0; i < 2; i++) begin
      if (instr_list[i].instr_name == LUI) begin
        instr_list[i].comment = $sformatf("corev_jalr_pma_undefined_region_instr: address: %0x", fwd_addr);
      end
    end
  endfunction : post_randomize
endclass : corev_jalr_pma_undefined_region_instr

// #############################################################################
//
// Section 3: Atomic operations test streams
//
// Note : amo-tests require A-extension enabled in config
//
// #############################################################################

// -----------------------------------------------------------------------------
//
// corev_pma_atomic_instr_stream_base
//
// -----------------------------------------------------------------------------
class corev_pma_atomic_instr_stream_base extends riscv_directed_instr_stream;
  cv32e40x_pma_cfg pma_cfg;
  mem_region_t data_page[$];
  int max_data_page_id;
  rand riscv_reg_t fwd_addr_reg[];
  rand bit [31:0] fwd_addr;
  rand int num_mixed_instr;
  rand int num_amo_instr;
  rand int num_fwd_addr_reg;
  rand int index;

  constraint num_fwd_addr_reg_c {
    num_fwd_addr_reg == 1;
  }

  constraint fwd_addr_reg_c {
    solve num_fwd_addr_reg before fwd_addr_reg;
    fwd_addr_reg.size() == num_fwd_addr_reg;
    foreach (fwd_addr_reg[i]) {
      !(fwd_addr_reg[i] inside {cfg.reserved_regs, reserved_rd, ZERO});
    }
    unique {fwd_addr_reg};
  }

  // Inside region constraint - override if need to hit undefined regions
  constraint valid_region_c {
    fwd_addr inside {[pma_cfg.regions[index].word_addr_low<<2:pma_cfg.regions[index].word_addr_high<<2]};
  }

  constraint valid_index_c {
    index inside {[0 : pma_cfg.pma_num_regions - 1]};
  }

  `uvm_object_utils(corev_pma_atomic_instr_stream_base)

  function new(string name = "");
    super.new(name);
    pma_cfg = cv32e40x_pma_cfg::type_id::create("pma_cfg");
  endfunction : new

  function void pre_randomize();
    data_page = cfg.mem_region;
    max_data_page_id = data_page.size();
    super.pre_randomize();
  endfunction : pre_randomize

  function void post_randomize();
    gen_amo_instr();
    reserved_rd = { reserved_rd, fwd_addr_reg };
    add_mixed_instr(num_mixed_instr);
    super.post_randomize();
  endfunction : post_randomize

  // Mix in some other instructions
  virtual function void add_mixed_instr(int instr_cnt);
    riscv_instr      instr;
    setup_allowed_instr(1, 1);
    for(int i = 0; i < instr_cnt; i ++) begin
      instr = riscv_instr::type_id::create("instr");
      randomize_instr(instr);
      insert_instr(instr);
    end
  endfunction

  virtual function void load_target_addr();
    riscv_instr instr;
    instr = riscv_instr::get_rand_instr(.include_instr({LUI}));
    foreach (fwd_addr_reg[i]) begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        instr_name == LUI;
        rd == fwd_addr_reg[i];
        fwd_addr[11] -> imm == (fwd_addr[31:12] + 1);
        !fwd_addr[11] -> imm == fwd_addr[31:12];
        , "Failed randomizing LUI"
      )
      instr.comment = $sformatf("Loading upper bits of addr: %0x (imm: %0x, region: %0d)", fwd_addr, instr.imm, index);
      insert_instr(instr, 0);

      instr = riscv_instr::get_rand_instr(.include_instr({ADDI}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        instr_name == ADDI;
        rs1 == fwd_addr_reg[i];
        rd == fwd_addr_reg[i];
        imm == fwd_addr[11:0];
        , "Failed randomizing ADDI"
      )
      instr.comment = $sformatf("end load_target_addr: %0x, %0s", fwd_addr, fwd_addr_reg[i].name());
      insert_instr(instr, 1);
    end
  endfunction : load_target_addr

  virtual function void gen_amo_instr();
  endfunction : gen_amo_instr

endclass : corev_pma_atomic_instr_stream_base

// -----------------------------------------------------------------------------
//
// corev_pma_atomic_random_instr_stream
//
// -----------------------------------------------------------------------------
class corev_pma_atomic_random_instr_stream extends corev_pma_atomic_instr_stream_base;
  riscv_instr lr_instr;
  riscv_instr sc_instr;

  constraint legal_c {
    num_amo_instr == 1;
    num_mixed_instr inside {[0:14]};
  }

  `uvm_object_utils(corev_pma_atomic_random_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual function void gen_amo_instr();
    riscv_instr_name_t allowed_lr_instr[];
    riscv_instr_name_t allowed_sc_instr[];
    allowed_lr_instr = {LR_W};
    allowed_sc_instr = {SC_W};
    foreach (fwd_addr_reg[i]) begin
      lr_instr = riscv_instr::get_rand_instr(.include_instr({ allowed_lr_instr }));
      sc_instr = riscv_instr::get_rand_instr(.include_instr({ allowed_sc_instr }));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(lr_instr,
        rs1 == fwd_addr_reg[i];
        if (reserved_rd.size() > 0) {
          !(rd inside { reserved_rd });
        }
        if (cfg.reserved_regs.size() > 0) {
          !(rd inside { cfg.reserved_regs });
        }
        rd != fwd_addr_reg[i];
      )
      lr_instr.comment = "LR";
      `DV_CHECK_RANDOMIZE_WITH_FATAL(sc_instr,
        rs1 == fwd_addr_reg[i];
        if (reserved_rd.size() > 0) {
          !(rd inside { reserved_rd });
        }
        if (cfg.reserved_regs.size() > 0) {
          !(rd inside { cfg.reserved_regs });
        }
        rd != fwd_addr_reg[i];
      )
      sc_instr.comment = "SC";
      instr_list.push_back(lr_instr);
      instr_list.push_back(sc_instr);
    end
  endfunction : gen_amo_instr

  // section 8.3 Eventual Success of Store-Conditional Instructions
  // An LR/SC sequence begins with an LR instruction and ends with an SC instruction.
  // The dynamic code executed between the LR and SC instructions can only contain
  // instructions from the base “I” instruction set, excluding loads, stores, backward
  // jumps, taken backward branches, JALR, FENCE, and SYSTEM instructions. If the “C”
  // extension is supported, then compressed forms of the aforementioned “I” instructions
  // are also permitted.
  virtual function void add_mixed_instr(int instr_cnt);
    riscv_instr instr;
    int i;
    setup_allowed_instr(.no_branch(1), .no_load_store(1));
    while (i < instr_cnt) begin
      instr = riscv_instr::type_id::create("instr");
      randomize_instr(instr, .include_group({RV32I, RV32C}));
      if (!(instr.category inside {SYNCH, SYSTEM})) begin
        insert_instr(instr);
        i++;
      end
    end
  endfunction

  function void pre_randomize();
    super.pre_randomize();
  endfunction : pre_randomize

  function void post_randomize();
    load_target_addr();
    super.post_randomize();
  endfunction : post_randomize

endclass : corev_pma_atomic_random_instr_stream

// -----------------------------------------------------------------------------
//
// corev_pma_atomic_amo_instr_stream
//
// -----------------------------------------------------------------------------
class corev_pma_atomic_amo_instr_stream extends corev_pma_atomic_instr_stream_base;
  riscv_instr amo_instr[];

  constraint reasonable_c {
    solve num_amo_instr before num_mixed_instr;
    num_amo_instr inside {[1 : 10]};
    num_mixed_instr inside {[0 : num_amo_instr]};
  }

  constraint num_fwd_addr_reg_c {
    solve num_amo_instr before num_fwd_addr_reg;
    num_fwd_addr_reg inside {[1 : num_amo_instr]};
    num_fwd_addr_reg < 5;
  }

  `uvm_object_utils(corev_pma_atomic_amo_instr_stream)
  `uvm_object_new

  virtual function void gen_amo_instr();
    amo_instr = new[num_amo_instr];
    foreach (amo_instr[i]) begin
      amo_instr[i] = riscv_instr::get_rand_instr(.include_category({ AMO }));
      amo_instr[i].print();
      `DV_CHECK_RANDOMIZE_WITH_FATAL(amo_instr[i],
        //rs1 == fwd_addr_reg[i];
        if (reserved_rd.size() > 0) {
          !(rd inside {reserved_rd});
        }
        if (cfg.reserved_regs.size() > 0) {
          !(rd inside {cfg.reserved_regs});
        }
        rs1 inside { fwd_addr_reg };
        !(rd inside { fwd_addr_reg });
        , $sformatf("rs1: %0d, fwd_addr_reg[i]: %0d, i: %0d", amo_instr[i].rs1, fwd_addr_reg[i], i)
      )
      instr_list.push_front(amo_instr[i]);
    end // foreach (amo_instr[i])
  endfunction : gen_amo_instr

endclass : corev_pma_atomic_amo_instr_stream

// -----------------------------------------------------------------------------
//
// corev_pma_atomic_aligned_instr_stream
//
// -----------------------------------------------------------------------------
class corev_pma_atomic_aligned_instr_stream extends corev_pma_atomic_random_instr_stream;

  constraint aligned_addr_c {
    (fwd_addr % 4) == 0;
  }

  `uvm_object_utils(corev_pma_atomic_aligned_instr_stream)
  `uvm_object_new

endclass : corev_pma_atomic_aligned_instr_stream

// -----------------------------------------------------------------------------
//
// corev_pma_atomic_misaligned_instr_stream
//
// -----------------------------------------------------------------------------
class corev_pma_atomic_misaligned_instr_stream extends corev_pma_atomic_random_instr_stream;

  constraint aligned_addr_c {
    (fwd_addr % 4) != 0;
  }

  `uvm_object_utils(corev_pma_atomic_misaligned_instr_stream)
  `uvm_object_new

endclass : corev_pma_atomic_misaligned_instr_stream

// -----------------------------------------------------------------------------
//
// corev_pma_atomic_allowed_instr_stream
//
// -----------------------------------------------------------------------------
class corev_pma_atomic_allowed_instr_stream extends corev_pma_atomic_random_instr_stream;

  constraint atomic_allowed_c {
    pma_cfg.regions[index].atomic == 1'b1;
  }

  `uvm_object_utils(corev_pma_atomic_allowed_instr_stream)
  `uvm_object_new

endclass : corev_pma_atomic_allowed_instr_stream

// -----------------------------------------------------------------------------
//
// corev_pma_atomic_disallowed_instr_stream
//
// -----------------------------------------------------------------------------
class corev_pma_atomic_disallowed_instr_stream extends corev_pma_atomic_random_instr_stream;

  constraint atomic_disallowed_c {
    pma_cfg.regions[index].atomic == 1'b0;
  }

  `uvm_object_utils(corev_pma_atomic_disallowed_instr_stream)
  `uvm_object_new

endclass : corev_pma_atomic_disallowed_instr_stream



