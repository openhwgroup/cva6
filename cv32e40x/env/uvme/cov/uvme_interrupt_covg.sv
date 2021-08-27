///////////////////////////////////////////////////////////////////////////////
// Copyright 2020 OpenHW Group
// Copyright 2020 BTA Design Services
// Copyright 2020 Silicon Labs, Inc.
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
//
///////////////////////////////////////////////////////////////////////////////

`uvm_analysis_imp_decl(_interrupt)
`uvm_analysis_imp_decl(_instr)

/*
* Covergroups
*/
covergroup cg_irq_entry(string name,
                        bit ext_m_supported,
                        bit ext_c_supported,
                        bit ext_zba_supported,
                        bit ext_zbb_supported,
                        bit ext_zbc_supported,
                        bit ext_zbs_supported,
                        bit ext_a_supported)
with function sample(uvma_isacov_instr_c instr);
    option.name = name;
    `per_instance_fcov
    cp_irq : coverpoint(instr.name) {
        `ISACOV_IGN_BINS
        // These instructions will enter the exception handler which will gate off any interrupts
        // by disabling MSIE immediately upon execution
        ignore_bins ebreak_excp   = { EBREAK };
        ignore_bins c_ebreak_excp = { C_EBREAK };
        ignore_bins ecal_excp     = { ECALL };
    }
endgroup : cg_irq_entry

covergroup cg_wfi_entry(string name,
                        bit ext_m_supported,
                        bit ext_c_supported,
                        bit ext_zba_supported,
                        bit ext_zbb_supported,
                        bit ext_zbc_supported,
                        bit ext_zbs_supported,
                        bit ext_a_supported)
with function sample(uvma_isacov_instr_c instr);
    option.name = name;
    `per_instance_fcov
    cp_wfi : coverpoint instr.name {
        `ISACOV_IGN_BINS
    }
endgroup : cg_wfi_entry

covergroup cg_irq_exit(string name,
                        bit ext_m_supported,
                        bit ext_c_supported,
                        bit ext_zba_supported,
                        bit ext_zbb_supported,
                        bit ext_zbc_supported,
                        bit ext_zbs_supported,
                        bit ext_a_supported)
with function sample(uvma_isacov_instr_c instr);
    option.name = name;
    `per_instance_fcov
    cp_irq : coverpoint instr.name {
        `ISACOV_IGN_BINS
        // Should not exit an IRQ into an MRET (usually interrupts are disabled at end of ISR)
        ignore_bins mret_excp = { MRET };
        // Should not exit an IRQ into a DRET
        ignore_bins dret_excp = { DRET };
    }
endgroup : cg_irq_exit

covergroup cg_wfi_exit(string name,
                        bit ext_m_supported,
                        bit ext_c_supported,
                        bit ext_zba_supported,
                        bit ext_zbb_supported,
                        bit ext_zbc_supported,
                        bit ext_zbs_supported,
                        bit ext_a_supported)
with function sample(uvma_isacov_instr_c instr);
    option.name = name;
    `per_instance_fcov
    cp_wfi : coverpoint instr.name {
        `ISACOV_IGN_BINS
    }
endgroup : cg_wfi_exit

class uvme_interrupt_covg extends uvm_component;

    /*
    * Class members
    */

    uvma_core_cntrl_cfg_c cfg;

    int unsigned irq_nested_count; // Count interrupt entry count for functional coverage

    uvma_isacov_mon_trn_c  last_instr_trn;

    cg_irq_entry irq_entry_cg;
    cg_wfi_entry wfi_entry_cg;
    cg_irq_exit  irq_exit_cg;
    cg_wfi_exit  wfi_exit_cg;

    uvm_analysis_imp_interrupt#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvme_interrupt_covg) interrupt_mon_export;
    uvm_analysis_imp_instr#(uvma_isacov_mon_trn_c, uvme_interrupt_covg) instr_mon_export;

    `uvm_component_utils(uvme_interrupt_covg);

    extern function new(string name = "interrupt_covg", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);

    extern function void write_interrupt(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);
    extern function void write_instr(uvma_isacov_mon_trn_c trn);

endclass : uvme_interrupt_covg

function uvme_interrupt_covg::new(string name = "interrupt_covg", uvm_component parent = null);

    super.new(name, parent);

    irq_nested_count = 0;


    interrupt_mon_export = new("interrupt_mon_export", this);
    instr_mon_export     = new("instr_mon_export", this);

endfunction : new

function void uvme_interrupt_covg::build_phase(uvm_phase phase);

    super.build_phase(phase);

    void'(uvm_config_db#(uvma_core_cntrl_cfg_c)::get(this, "", "cfg", cfg));
    if (!cfg) begin
        `uvm_fatal("CFG", "Configuration handle is null")
    end

    irq_entry_cg = new("irq_entry",
                       .ext_m_supported(cfg.ext_m_supported),
                       .ext_c_supported(cfg.ext_c_supported),
                       .ext_zba_supported(cfg.ext_zba_supported),
                       .ext_zbb_supported(cfg.ext_zbb_supported),
                       .ext_zbc_supported(cfg.ext_zbc_supported),
                       .ext_zbs_supported(cfg.ext_zbs_supported),
                       .ext_a_supported(cfg.ext_a_supported));

    wfi_entry_cg = new("wfi_entry",
                       .ext_m_supported(cfg.ext_m_supported),
                       .ext_c_supported(cfg.ext_c_supported),
                       .ext_zba_supported(cfg.ext_zba_supported),
                       .ext_zbb_supported(cfg.ext_zbb_supported),
                       .ext_zbc_supported(cfg.ext_zbc_supported),
                       .ext_zbs_supported(cfg.ext_zbs_supported),
                       .ext_a_supported(cfg.ext_a_supported));

    irq_exit_cg  = new("irq_exit",
                       .ext_m_supported(cfg.ext_m_supported),
                       .ext_c_supported(cfg.ext_c_supported),
                       .ext_zba_supported(cfg.ext_zba_supported),
                       .ext_zbb_supported(cfg.ext_zbb_supported),
                       .ext_zbc_supported(cfg.ext_zbc_supported),
                       .ext_zbs_supported(cfg.ext_zbs_supported),
                       .ext_a_supported(cfg.ext_a_supported));

    wfi_exit_cg  = new("wfi_exit",
                       .ext_m_supported(cfg.ext_m_supported),
                       .ext_c_supported(cfg.ext_c_supported),
                       .ext_zba_supported(cfg.ext_zba_supported),
                       .ext_zbb_supported(cfg.ext_zbb_supported),
                       .ext_zbc_supported(cfg.ext_zbc_supported),
                       .ext_zbs_supported(cfg.ext_zbs_supported),
                       .ext_a_supported(cfg.ext_a_supported));

endfunction : build_phase

task uvme_interrupt_covg::run_phase(uvm_phase phase);

    super.run_phase(phase);

    `uvm_info("INTERRUPTCOVG", "The interrupt coverage model is running", UVM_LOW);

endtask : run_phase

function void uvme_interrupt_covg::write_interrupt(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);

    if (trn.intr == 1 && last_instr_trn != null) begin
        `uvm_info("INTERRUPTCOVG", $sformatf("IRQ entered from %s", last_instr_trn.instr.name.name()), UVM_DEBUG)
        irq_entry_cg.sample(last_instr_trn.instr);
        irq_nested_count++;
    end

endfunction : write_interrupt

function void uvme_interrupt_covg::write_instr(uvma_isacov_mon_trn_c trn);

    // If this is a WFI, then sample the last instruction
    if (trn.instr.name == WFI && last_instr_trn != null) begin
        wfi_entry_cg.sample(last_instr_trn.instr);
    end

    // If last instruction was WFI, then sample exit WFI coverage
    if (last_instr_trn != null && last_instr_trn.instr.name == WFI) begin
        `uvm_info("INTERRUPTCOVG", $sformatf("WFI Exit: instruction is %s", trn.instr.name.name()), UVM_DEBUG)
        wfi_exit_cg.sample(trn.instr);
    end

    // For each mret decrement the interrupt count
    if (last_instr_trn != null && last_instr_trn.instr.name == MRET && irq_nested_count) begin
        `uvm_info("INTERRUPTCOVG", $sformatf("IRQ exited to %s", trn.instr.name.name()), UVM_DEBUG)
        irq_exit_cg.sample(trn.instr);
        irq_nested_count--;
    end

    // When an instruction is sampled, just save the handle here
    // It will be sampled when an interrupt or wfi event occurs
    last_instr_trn = trn;

endfunction : write_instr
