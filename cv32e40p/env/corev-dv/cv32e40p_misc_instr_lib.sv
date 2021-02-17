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
 * corev_jal_wfi_instr: Directed test stream that uses the riscv_jal_instr directed instruction stream and injects random
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

/*
 * corev_nop_instr
 *
 * Generates a compressed or non-compressed NOP (pseduo-op)
 */
 
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

/*
 * corev_xori_not_instr
 *
 * Generates a XORI with a -1 immediate value to tesdt logical not pseudo-op
 */
 
class corev_xori_not_instr extends riscv_directed_instr_stream;

  `uvm_object_utils(corev_xori_not_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr_name_t allowed_xori[$];
    riscv_instr        xori;

    allowed_xori.push_back(XORI);

    xori = riscv_instr::get_rand_instr(.include_instr(allowed_xori));
    xori.m_cfg = cfg;
    randomize_gpr(xori);
    xori.imm = -1;
    xori.extend_imm();
    xori.update_imm_str();
    xori.comment = "corev_xori_not_instr";
    insert_instr(xori, 0);
  endfunction : post_randomize

endclass : corev_xori_not_instr

/*
 * corev_jalr_wfi_instr
 *
 * Create a very directed test stream to close coverage on wfi followed by a jump
 * The directed stream will run a fixed sequence like so: (Note that flavors of jumps are randomized when allowable by the ISA)
 *    la         s0, 1f #start corev_jalr_wfi_instr
 *    la         s1, 2f
 *    wfi
 *    jalr       zero, s0, 0
 * 2: c.jal      3f
 * 1: jalr       zero, s1, 0
 * 3: nop
 */
class corev_jalr_wfi_instr extends riscv_directed_instr_stream;

  rand bit         use_jalr;
  rand bit         use_compressed;
  rand riscv_reg_t fwd_addr_reg;
  rand riscv_reg_t bwd_addr_reg;

  constraint use_jalr_c {
    // Compressed versions of jalr can only use ra, so we can only use ra if not reserved
    (RA inside {cfg.reserved_regs}) -> !use_jalr;
  }

  constraint use_compressed_c {
    cfg.disable_compressed_instr -> !use_compressed;
    use_compressed == 1;
  }

  constraint valid_reg_c {
    fwd_addr_reg != bwd_addr_reg;
    !(fwd_addr_reg inside {cfg.reserved_regs});
    !(bwd_addr_reg inside {cfg.reserved_regs});
    // Always use compressed instruction targetable register
    use_compressed -> (fwd_addr_reg inside {[S0:A5]});
    use_compressed -> (bwd_addr_reg inside {[S0:A5]});
  }

  `uvm_object_utils(corev_jalr_wfi_instr);

  function new(string name = "");
    super.new(name);
  endfunction : new
  
  function void post_randomize();
    riscv_pseudo_instr la_instr;
    riscv_instr        instr;
    riscv_instr_name_t allowed_instr[];

    // ---------------------------------------
    // First instruction: load the address of fwd label (1)    
    // ---------------------------------------
    la_instr = riscv_pseudo_instr::type_id::create("LA");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(la_instr,
      pseudo_instr_name == LA;
      rd == fwd_addr_reg;
      , "Failed randomizing LA"
    )
    la_instr.imm_str = "1f";
    la_instr.comment = "start corev_jalr_wfi_instr";    
    insert_instr(la_instr, 0);

    // ---------------------------------------
    // Second instruction: load the address of bwd label (2)
    // ---------------------------------------
    la_instr = riscv_pseudo_instr::type_id::create("LA");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(la_instr,
      pseudo_instr_name == LA;
      rd == bwd_addr_reg;
      , "Failed randomizing LA"
    )
    la_instr.imm_str = "2f";
    insert_instr(la_instr, 1);

    // ---------------------------------------
    // WFI
    // ---------------------------------------
    instr = riscv_instr::get_instr(WFI);
    instr.m_cfg = cfg;
    insert_instr(instr, 2);

    // ---------------------------------------
    // Jump to routine
    // ---------------------------------------
    allowed_instr = {JALR};
    if (use_compressed) begin
      allowed_instr = {allowed_instr, C_JR};
      if (use_jalr) begin
        allowed_instr = {allowed_instr, C_JALR};
      end
    end
    instr = riscv_instr::get_rand_instr(.include_instr(allowed_instr));    
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,    
      instr_name == JALR -> rd == ZERO;
      rs1 == fwd_addr_reg;
      , "Could not randomize JR"
    )
    instr.imm_str = "0";
    insert_instr(instr, 3);

    // ---------------------------------------
    // Jump to end (label 3)
    // ---------------------------------------
    allowed_instr = {JAL};
    if (use_compressed) begin
      allowed_instr = {allowed_instr, C_J, C_JAL};
    end
    //instr = riscv_instr::type_id::create("LI");
    instr = riscv_instr::get_rand_instr(.include_instr(allowed_instr));    
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,      
      (instr_name inside {JALR, JAL}) -> rd == ZERO;      
      , "Could not randomize jump"
    )
    instr.imm_str = "3f";
    instr.label   = "2";       
    insert_instr(instr, 4);

    // ---------------------------------------
    // Jump back (label 1)
    // ---------------------------------------
    allowed_instr = {JALR};
    if (use_compressed) begin
      allowed_instr = {allowed_instr, C_JR};
      if (use_jalr) begin
        allowed_instr = {allowed_instr, C_JALR};
      end
    end
    instr = riscv_instr::get_rand_instr(.include_instr(allowed_instr));    
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,      
      instr_name == JALR -> rd == ZERO;
      rs1 == bwd_addr_reg;
      , "Could not randomize jump back"
    )
    instr.imm_str = "0";
    instr.label   = "1";
    insert_instr(instr, 5);

    // ---------------------------------------
    // Final instruction (NOP)
    // ---------------------------------------
    instr = riscv_instr::get_instr(NOP);
    instr.label  = "3";    
    insert_instr(instr, 6);

    foreach(instr_list[i]) begin
      instr_list[i].atomic = 1;
      if(instr_list[i].label == "")
        instr_list[i].has_label = 0;
    end

  endfunction : post_randomize

endclass : corev_jalr_wfi_instr