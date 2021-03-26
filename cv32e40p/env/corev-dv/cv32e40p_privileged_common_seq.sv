/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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

//-----------------------------------------------------------------------------------------
// CORE-V privileged mode sequence customizations
//
// Overrides setup_mmode_reg()
//-----------------------------------------------------------------------------------------

class cv32e40p_privileged_common_seq extends riscv_privileged_common_seq;

    `uvm_object_utils(cv32e40p_privileged_common_seq)

    function new(string name = "");
        super.new(name);
    endfunction

    // Override this function to avoid setting MIE before mret call to prevent
    // infinite loop
    virtual function void setup_mmode_reg(privileged_mode_t mode, ref riscv_privil_reg regs[$]);
      mstatus = riscv_privil_reg::type_id::create("mstatus");
      mstatus.init_reg(MSTATUS);
      if (cfg.randomize_csr) begin
        mstatus.set_val(cfg.mstatus);
      end
      mstatus.set_field("MPRV", cfg.mstatus_mprv);
      mstatus.set_field("MXR", cfg.mstatus_mxr);
      mstatus.set_field("SUM", cfg.mstatus_sum);
      mstatus.set_field("TVM", cfg.mstatus_tvm);
      mstatus.set_field("TW", cfg.set_mstatus_tw);
      mstatus.set_field("FS", cfg.mstatus_fs);
      mstatus.set_field("VS", cfg.mstatus_vs);
      if (!(SUPERVISOR_MODE inside {supported_privileged_mode}) && (XLEN != 32)) begin
        mstatus.set_field("SXL", 2'b00);
      end else if (XLEN == 64) begin
        mstatus.set_field("SXL", 2'b10);
      end
      if (!(USER_MODE inside {supported_privileged_mode}) && (XLEN != 32)) begin
        mstatus.set_field("UXL", 2'b00);
      end else if (XLEN == 64) begin
        mstatus.set_field("UXL", 2'b10);
      end
      mstatus.set_field("XS", 0);
      mstatus.set_field("SD", 0);
      mstatus.set_field("UIE", 0);
      // Set the previous privileged mode as the target mode
      mstatus.set_field("MPP", mode);
      mstatus.set_field("SPP", 0);
      // Enable interrupt
      mstatus.set_field("MPIE", cfg.enable_interrupt);
      // MIE will be set by mret, avoid trapping before returning from this
      // setup function
      mstatus.set_field("MIE", 0);
      mstatus.set_field("SPIE", cfg.enable_interrupt);
      mstatus.set_field("SIE",  cfg.enable_interrupt);
      mstatus.set_field("UPIE", cfg.enable_interrupt);
      mstatus.set_field("UIE", riscv_instr_pkg::support_umode_trap);
      `uvm_info(`gfn, $sformatf("mstatus_val: 0x%0x", mstatus.get_val()), UVM_LOW)
      regs.push_back(mstatus);
      // Enable external and timer interrupt
      if (MIE inside {implemented_csr}) begin
        mie = riscv_privil_reg::type_id::create("mie");
        mie.init_reg(MIE);
        if (cfg.randomize_csr) begin
          mie.set_val(cfg.mie);
        end
        mie.set_field("UEIE", cfg.enable_interrupt);
        mie.set_field("SEIE", cfg.enable_interrupt);
        mie.set_field("MEIE", cfg.enable_interrupt);
        mie.set_field("USIE", cfg.enable_interrupt);
        mie.set_field("SSIE", cfg.enable_interrupt);
        mie.set_field("MSIE", cfg.enable_interrupt);
        mie.set_field("MTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
        mie.set_field("STIE", cfg.enable_interrupt & cfg.enable_timer_irq);
        mie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
        regs.push_back(mie);
      end
    endfunction : setup_mmode_reg

endclass : cv32e40p_privileged_common_seq
