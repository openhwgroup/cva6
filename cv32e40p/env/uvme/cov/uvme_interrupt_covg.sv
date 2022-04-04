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
`uvm_analysis_imp_decl(_rv32isa)

class uvme_interrupt_covg extends uvm_component;

    /*
    * Covergroups
    */
    covergroup cg_irq_entry with function sample(ins_t ins);
        `per_instance_fcov
        cp_irq : coverpoint ins.asm {
            // These instructions will enter the exception handler which will gate off any interrupts
            // by disabling MSIE immediately upon execution
            ignore_bins ebreak_excp   = { EBREAK };
            ignore_bins c_ebreak_excp = { C_EBREAK };
            ignore_bins ecal_excp     = { ECALL };
        }
    endgroup : cg_irq_entry

    covergroup cg_wfi_entry with function sample(ins_t ins);
        `per_instance_fcov
        cp_wfi : coverpoint ins.asm {
        }
    endgroup : cg_wfi_entry

    covergroup cg_irq_exit with function sample(ins_t ins);
        `per_instance_fcov
        cp_irq : coverpoint ins.asm {
            // Should not exit an IRQ into an MRET (usually interrupts are disabled at end of ISR)
            ignore_bins mret_excp = { MRET };
            // Should not exit an IRQ into a DRET
            ignore_bins dret_excp = { DRET };
        }
    endgroup : cg_irq_exit

    covergroup cg_wfi_exit with function sample(ins_t ins);
        `per_instance_fcov
        cp_wfi : coverpoint ins.asm {
        }
    endgroup : cg_wfi_exit

    /*
    * Class members
    */

    int unsigned irq_nested_count; // Count interrupt entry count for functional coverage

    uvme_rv32isa_covg_trn_c  last_instr_trn;

    uvm_analysis_imp_interrupt#(uvma_interrupt_mon_trn_c, uvme_interrupt_covg) interrupt_mon_export;
    uvm_analysis_imp_rv32isa#(uvme_rv32isa_covg_trn_c, uvme_interrupt_covg)    rv32isa_export;

    `uvm_component_utils(uvme_interrupt_covg);

    extern function new(string name = "interrupt_covg", uvm_component parent = null);
    extern task run_phase(uvm_phase phase);

    extern function void write_interrupt(uvma_interrupt_mon_trn_c trn);
    extern function void write_rv32isa(uvme_rv32isa_covg_trn_c trn);
endclass : uvme_interrupt_covg

function uvme_interrupt_covg::new(string name = "interrupt_covg", uvm_component parent = null);
    super.new(name, parent);

    irq_nested_count = 0;

    cg_irq_entry = new();
    cg_wfi_entry = new();
    cg_irq_exit  = new();
    cg_wfi_exit  = new();

    interrupt_mon_export = new("interrupt_mon_export", this);
    rv32isa_export = new("rv32isa_export", this);
endfunction : new

task uvme_interrupt_covg::run_phase(uvm_phase phase);
    super.run_phase(phase);

    `uvm_info("INTERRUPTCOVG", "The interrupt coverage model is running", UVM_LOW);

endtask : run_phase

function void uvme_interrupt_covg::write_interrupt(uvma_interrupt_mon_trn_c trn);
    if (trn.action == UVMA_INTERRUPT_MON_ACTION_IRQ && last_instr_trn != null) begin
        `uvm_info("INTERRUPTCOVG", $sformatf("IRQ entered from %s", last_instr_trn.ins.asm.name()), UVM_DEBUG)
        cg_irq_entry.sample(last_instr_trn.ins);
        irq_nested_count++;
    end
endfunction : write_interrupt

function void uvme_interrupt_covg::write_rv32isa(uvme_rv32isa_covg_trn_c trn);

    // If this is a WFI, then sample the last instruction
    if (trn.ins.asm == WFI && last_instr_trn != null) begin
        cg_wfi_entry.sample(last_instr_trn.ins);
    end

    // If last instruction was WFI, then sample exit WFI coverage
    if (last_instr_trn != null && last_instr_trn.ins.asm == WFI) begin
        `uvm_info("INTERRUPTCOVG", $sformatf("WFI Exit: instruction is %s", trn.ins.asm.name()), UVM_DEBUG)
        cg_wfi_exit.sample(trn.ins);
    end

    // For each mret decrement the interrupt count
    if (last_instr_trn != null && last_instr_trn.ins.asm == MRET && irq_nested_count) begin
        `uvm_info("INTERRUPTCOVG", $sformatf("IRQ exited to %s", trn.ins.asm.name()), UVM_DEBUG)
        cg_irq_exit.sample(trn.ins);
        irq_nested_count--;
    end

    // When an instruction is sampled, just save the handle here
    // It will be sampled when an interrupt or wfi event occurs
    last_instr_trn = trn;
endfunction : write_rv32isa
