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
 * corev_interrupt_csr_instr_stream
 *
 * Directed test stream to inject CLINT-interrupt related CSR writes
 * Randomly selects one of the following via weights
 * - Random write to MIE register
 * - Random write to MSTATUS.MIE register
 */

class corev_interrupt_csr_instr_stream extends riscv_load_store_rand_instr_stream;

  typedef enum { 
    RANDOM_MIE,
    RANDOM_MSTATUS_MIE
  } interrupt_csr_action_enum;

  rand interrupt_csr_action_enum action;
`ifdef _VCP
  int unsigned wgt_random_mie = 1;
  int unsigned wgt_random_mstatus_mie = 3;
`else
  rand int unsigned wgt_random_mie;
  rand int unsigned wgt_random_mstatus_mie;
`endif
  rand reg[31:0] rand_mie_setting;
`ifndef _VCP
  constraint ordering_wgt_c {
    solve wgt_random_mie before action;
    solve wgt_random_mstatus_mie before action;
  }
`endif
  constraint dist_action_c {
    action dist  { RANDOM_MIE :/ wgt_random_mie,
                   RANDOM_MSTATUS_MIE :/ wgt_random_mstatus_mie };
  }
`ifndef _VCP
  constraint default_wgt_c {
    soft wgt_random_mie == 1;
    soft wgt_random_mstatus_mie == 3; 
  }
`endif

  riscv_instr_name_t allowed_mie_instr[$] = {CSRRW, CSRRC, CSRRS};

  `uvm_object_utils(corev_interrupt_csr_instr_stream)
  `uvm_object_new

  function void post_randomize();
    super.post_randomize();
  endfunction : post_randomize

  virtual function void add_mixed_instr(int instr_cnt);
    super.add_mixed_instr(instr_cnt);

    case (action)
      RANDOM_MIE: generate_mie_write();
      RANDOM_MSTATUS_MIE: generate_mstatus_mie_write();
    endcase
  endfunction : add_mixed_instr

  function void generate_mie_write();
    riscv_instr        inserted_instr_list[$];

    riscv_pseudo_instr li_instr;
    riscv_instr        csr_instr;

    // Instruction 0: Generate a li with a randomized mask
    li_instr = riscv_pseudo_instr::type_id::create("LI");  
    `DV_CHECK_RANDOMIZE_WITH_FATAL(li_instr,
      pseudo_instr_name == LI;
      !(rd inside {reserved_rd, cfg.reserved_regs});
      , "Failed randomizeing MIE LI instruction"
    )
    // riscv_instr constraints don't handle psuedo-op LI immediate correctly (gets truncated)
    li_instr.imm = rand_mie_setting;
    li_instr.comment = $sformatf("corev-dv: Set MIE to 0x%08x", rand_mie_setting);
    li_instr.update_imm_str();
    inserted_instr_list.push_back(li_instr);
    
    // Instruction 1: Generate a write, set or clear to MIE
    csr_instr = riscv_instr::get_rand_instr(.include_instr(allowed_mie_instr));
    csr_instr.csr_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(csr_instr,
      csr == MIE;    
      !(rd inside {reserved_rd, cfg.reserved_regs});
      rs1 == li_instr.rd;
      , "Cannot randomize MIE CSR instruction"
    )
    inserted_instr_list.push_back(csr_instr);

    // Add to the random list of instructions
    insert_instr_stream(inserted_instr_list);
  endfunction : generate_mie_write

  function void generate_mstatus_mie_write();
    riscv_instr csr_instr;

    // Randomly set or clear bit 3 (MIE) in MSTATUS        
    csr_instr = riscv_instr::get_rand_instr(.include_instr({CSRRSI, CSRRCI}));
    csr_instr.csr_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(csr_instr,
      csr == MSTATUS;
      !(rd inside {reserved_rd, cfg.reserved_regs});
      imm inside {'h8, 'h0};
      , "Cannot randomize MSTATUS_MIE CSR instruction"
    )
    csr_instr.comment = "corev-dv: alter MSTATUS_MIE";
    insert_instr(csr_instr);
  endfunction : generate_mstatus_mie_write

endclass : corev_interrupt_csr_instr_stream

 