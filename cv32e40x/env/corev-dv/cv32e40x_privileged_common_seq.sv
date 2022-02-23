class cv32e40x_privileged_common_seq extends riscv_privileged_common_seq;

  `uvm_object_utils(cv32e40x_privileged_common_seq)

  function new(string name = "", uvm_component parent = null);
    super.new(name);
  endfunction : new

  virtual function void setup_mmode_reg(privileged_mode_t mode, ref riscv_privil_reg regs[$]);
    mstatus = riscv_privil_reg::type_id::create("mstatus");
    mstatus.init_reg(MSTATUS);
    if (cfg.randomize_csr) begin
      mstatus.set_val(cfg.mstatus);
    end
    mstatus.set_field("MPRV", cfg.mstatus_mprv);
    // Set the previous privileged mode as the target mode
    mstatus.set_field("MPP", mode);
    // Enable interrupt
    mstatus.set_field("MPIE", cfg.enable_interrupt);
    // MIE is set when returning with mret, avoids trapping before returning
    mstatus.set_field("MIE", 0);
    // Zero out the remaining fields to avoid issues with unimplemented features
    mstatus.set_field("WPRI0", 0);
    mstatus.set_field("WPRI1", 0);
    mstatus.set_field("WPRI2", 0);
    mstatus.set_field("WPRI3", 0);
    mstatus.set_field("WPRI4", 0);

    `uvm_info(`gfn, $sformatf("mstatus_val: 0x%0x", mstatus.get_val()), UVM_LOW)
    regs.push_back(mstatus);
    // Enable external and timer interrupt
    if (MIE inside {implemented_csr}) begin
      mie = riscv_privil_reg::type_id::create("mie");
      mie.init_reg(MIE);
      if (cfg.randomize_csr) begin
        mie.set_val(cfg.mie);
      end
      mie.set_field("MEIE", cfg.enable_interrupt);
      mie.set_field("MSIE", cfg.enable_interrupt);
      mie.set_field("MTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      regs.push_back(mie);
    end
  endfunction
endclass : cv32e40x_privileged_common_seq
