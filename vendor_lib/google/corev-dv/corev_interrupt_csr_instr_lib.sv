class corev_interrupt_csr_instr_stream extends riscv_rand_instr_stream;

  `uvm_object_utils(corev_interrupt_csr_instr_stream)
  `uvm_object_new

  function void post_randomize();
    `uvm_info("CVINTRRUPTCSRINSTR", "I am here", UVM_LOW)
    initialize_instr_list(1);
    allowed_instr = {CSRRW, CSRRS, CSRRC};

    foreach (instr_list[i]) begin
      randomize_instr(instr_list[i]);
      randcase
        1: generate_mie_write();
        1: generate_mstatus_mie_write();
      endcase
    end

  endfunction

  function void generate_mie_write();
    // Create a single MIE that can write, clear or set random bits unconstrained
    `uvm_info("CVINTRCSRINSTR", "Generate MIE", UVM_LOW)
    initialize_instr_list(.instr_cnt(1));

    instr_list[0] = riscv_instr::get_rand_instr(.include_instr({CSRRW, CSRRS, CSRRC}));
    instr_list[0].csr_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr_list[0],
      csr == MIE;,
      "Cannot randomize MIE CSR instruction"
    )    
  endfunction

  function void generate_mstatus_mie_write();
    // Randomly set or clear bit 3 (MIE) in MSTATUS    
    `uvm_info("CVINTRCSRINSTR", "Generate MSTATUS_MIE", UVM_LOW)
    
    initialize_instr_list(.instr_cnt(1));
    instr_list[0] = riscv_instr::get_rand_instr(.include_instr({CSRRWI, CSRRSI, CSRRCI}));
    instr_list[0].csr_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr_list[0],
      rd == ZERO;
      csr == MSTATUS;
      imm inside {'h4, 'h0};,
      "Cannot randomize MSTATUS_MIE CSR instruction"
    )
  endfunction

endclass : corev_interrupt_csr_instr_stream
