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


class uvme_debug_covg extends uvm_component;

    /*
    * Class members
    */
    uvme_cv32_cntxt_c  cntxt;


    `uvm_component_utils(uvme_debug_covg);

    extern function new(string name = "debug_covg", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);

    extern task sample_clk_i();
    extern task sample_debug_req_i();

    /*
    * Covergroups
    */
   
  covergroup cg_debug_mode_ext ;
          option.per_instance = 1;
          state: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.ctrl_fsm_cs;
  endgroup : cg_debug_mode_ext

  // Cover that we execute ebreak with dcsr.ebreakm==1
  covergroup cg_ebreak_execute_with_ebreakm;
          option.per_instance = 1;
          ex: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.is_ebreak {
                  bins active = {1};
          }
          ebreakm_set: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.dcsr_q[15] {
                  bins active = {1};
          }
          dm : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
                  bins active = {1};
          }
          ebreak_with_ebreakm: cross ex, ebreakm_set;  
          ebreak_in_debug : cross ex, dm;
  endgroup
    
  // Cover that we execute c.ebreak with dcsr.ebreakm==1
  covergroup cg_cebreak_execute_with_ebreakm;
          option.per_instance = 1;
          ex: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.is_cebreak {
                  bins active = {1};
          }
          ebreakm_set: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.dcsr_q[15] {
                  bins active = {1};
          }
          dm : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
                  bins active = {1};
          }
          cebreak_with_ebreakm: cross ex, ebreakm_set;  
          cebreak_in_debug : cross ex, dm;
  endgroup

  // Cover that we execute ebreak with dcsr.ebreakm==0
  covergroup cg_ebreak_execute_without_ebreakm;
          option.per_instance = 1;
          ex: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.is_ebreak {
                  bins active = {1};
          }
          ebreakm_clear: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.dcsr_q[15] {
                  bins active = {0};
          }
          test: cross ex, ebreakm_clear;  
  endgroup
    
  // Cover that we execute c.ebreak with dcsr.ebreakm==0
  covergroup cg_cebreak_execute_without_ebreakm;
          option.per_instance = 1;
          ex: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.is_cebreak {
                  bins active = {1};
          }
          ebreakm_clear: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.dcsr_q[15] {
                  bins active = {0};
          }
          test: cross ex, ebreakm_clear;  
  endgroup

    // Cover that we hit a trigger match
    covergroup cg_trigger_match;
        option.per_instance = 1;
        en : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.tdata1[2] {
            bins active = {1};
        }
        match: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.trigger_match_i {
            bins hit = {1};
        }
        ok_match: cross en, match;
    endgroup

    // cover that we hit pc==tdata2  without having enabled trigger in m/d-mode
    // cover hit in d-mode with trigger enabled (no action)
    covergroup cg_trigger_match_disabled;
        option.per_instance = 1;
        dis : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.tdata1[2] {
            bins hit = {0};
        }
        en : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.tdata1[2] {
            bins hit = {1};
        }
        match: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.addr_match {
           bins hit = {1};
        }
        mmode : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
           bins m = {0};
        }
        dmode : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
           bins m = {1};
        }
        m_match_without_en : cross dis, match, mmode;
        d_match_without_en : cross dis, match, dmode;
        d_match_with_en    : cross en, match, dmode;
    endgroup

    // Cover that we hit an exception during debug mode
    covergroup cg_debug_mode_exception;
        option.per_instance = 1;
        dm : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
            bins hit  = {1};
        }
        ill : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.illegal_insn_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, ill;
    endgroup

    // Cover that we hit an ecall during debug mode
    covergroup cg_debug_mode_ecall;
        option.per_instance = 1;
        dm : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
            bins hit  = {1};
        }
        ill : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.ecall_insn_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, ill;
    endgroup

    // Cover that we get interrupts while in debug mode
    covergroup cg_irq_in_debug;
        option.per_instance = 1;
        dm : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
            bins hit  = {1};
        }
        irq : coverpoint |cntxt.debug_cntxt.vif_cov.mon_cb.irq_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, irq;
    endgroup
    
    // Cover that hit a WFI insn in debug mode
    covergroup cg_wfi_in_debug;
        option.per_instance = 1;
        iswfi : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.is_wfi {
                bins hit  = {1};
        }
        dm : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
            bins hit = {1};
        }
        dm_wfi : cross iswfi, dm;
    endgroup

    // Cover that we get a debug_req while in wfi
    covergroup cg_wfi_debug_req;
        option.per_instance = 1;
        inwfi : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.in_wfi {
                bins hit  = {1};
        }
        dreq: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_req_i {
            bins hit = {1};
        }
        dm_wfi : cross inwfi, dreq;
    endgroup

    // Cover that we perform single stepping
    covergroup cg_single_step;
        option.per_instance = 1;
        step : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.dcsr_q[2] {
                bins en  = {1};
        }
        mmode: coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q {
            bins hit = {0};
        }
        trigger : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.trigger_match_i {
            bins hit = {1};
        }
        wfi : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.is_wfi {
            bins hit = {1};
        }
        ill : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.illegal_insn_i {
            bins hit = {1};
        }
        pc_will_trig : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.dpc_will_hit {
            bins hit = {1};
        } 
        stepie : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.dcsr_q[11];
        mmode_step : cross step, mmode;
        mmode_step_trigger_match : cross step, mmode, trigger;
        mmode_step_wfi : cross step, mmode, wfi;
        mmode_step_stepie : cross step, mmode, stepie;
        mmode_step_illegal : cross step, mmode, ill;
        mmode_step_next_pc_will_match : cross step, mmode, pc_will_trig;
    endgroup

    // Cover dret is executed in machine mode
    covergroup cg_mmode_dret;
        option.per_instance = 1;
        mmode : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q;
        dret_ins : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.is_dret {
            bins hit = {1};
        }
        dret_ex : cross mmode, dret_ins;
    endgroup

    // Cover debug_req and irq asserted on same cycle
    covergroup cg_irq_dreq;
        option.per_instance = 1;
        dreq : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_req_i {
                bins trans_active  = (1'b0 => 1'b1);
        }
        irq  : coverpoint |cntxt.debug_cntxt.vif_cov.mon_cb.irq_i {
                bins trans_active = (1'b0 => 1'b1);
        }
        irq_and_dreq : cross dreq, irq;
    endgroup

    // Cover access to dcsr, dpc and dscratch0/1
    // Do we need to cover all READ/WRITE/SET/CLEAR from m-mode?
    covergroup cg_debug_regs;
        option.per_instance = 1;
        mode : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q; // Only M and D supported
        access : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.csr_access {
            bins hit = {1};
        }
        op : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.csr_op {
            bins read = {'h0};
            bins write = {'h1};
        }
        addr  : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.id_stage_instr_rdata_i[31:20] { // csr addr not updated if illegal access
            bins dcsr = {'h7B0};
            bins dpc = {'h7B1};
            bins dscratch0 = {'h7B2};
            bins dscratch1 = {'h7B3};
        }
        dregs_access : cross mode, access, op,addr;
    endgroup

    // Cover access to trigger registers
    // Do we need to cover all READ/WRITE/SET/CLEAR from m-mode?
    covergroup cg_trigger_regs;
        option.per_instance = 1;
        mode : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.debug_mode_q; // Only M and D supported
        access : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.csr_access {
            bins hit = {1};
        }
        op : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.csr_op {
            bins read = {'h0};
            bins write = {'h1};
        }
        addr  : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.id_stage_instr_rdata_i[31:20]{ // csr addr not updated if illegal access
            bins tsel = {'h7A0};
            bins tdata1 = {'h7A1};
            bins tdata2 = {'h7A2};
            bins tdata3 = {'h7A3};
            bins tinfo = {'h7A4};
        }
        tregs_access : cross mode, access, op,addr;
    endgroup

    // Cover that we run with counters mcycle and minstret enabled
    covergroup cg_counters_enabled;
        option.per_instance = 1;
        mcycle_en : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.mcountinhibit_q[0];
        minstret_en : coverpoint cntxt.debug_cntxt.vif_cov.mon_cb.mcountinhibit_q[2];
    endgroup


endclass : uvme_debug_covg

function uvme_debug_covg::new(string name = "debug_covg", uvm_component parent = null);
    super.new(name, parent);

    cg_debug_mode_ext = new();
    cg_ebreak_execute_with_ebreakm = new();
    cg_cebreak_execute_with_ebreakm = new();
    cg_ebreak_execute_without_ebreakm = new();
    cg_cebreak_execute_without_ebreakm = new();
    cg_trigger_match = new();
    cg_trigger_match_disabled = new();
    cg_debug_mode_exception = new();
    cg_debug_mode_ecall = new();
    cg_irq_in_debug = new();
    cg_wfi_in_debug = new();
    cg_wfi_debug_req = new();
    cg_single_step = new();
    cg_mmode_dret = new();
    cg_irq_dreq = new();
    cg_debug_regs = new();
    cg_trigger_regs = new();
    cg_counters_enabled = new();

endfunction : new

function void uvme_debug_covg::build_phase(uvm_phase phase);
    super.build_phase(phase);

    void'(uvm_config_db#(uvme_cv32_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("DEBUGCOVG", "No cntxt object passed to model");
    end
endfunction : build_phase

task uvme_debug_covg::run_phase(uvm_phase phase);
    super.run_phase(phase);

    `uvm_info("DEBUGCOVG", "The debug coverage model is running", UVM_LOW);

    fork 
        sample_debug_req_i();
        sample_clk_i();
    join_none
endtask : run_phase

task uvme_debug_covg::sample_debug_req_i();
  while(1) begin
    @(posedge cntxt.debug_cntxt.vif_cov.mon_cb.debug_req_i);

    cg_debug_mode_ext.sample();
  end  
endtask : sample_debug_req_i

task uvme_debug_covg::sample_clk_i();
  while (1) begin
    @(cntxt.debug_cntxt.vif_cov.mon_cb);

    cg_ebreak_execute_with_ebreakm.sample();
    cg_cebreak_execute_with_ebreakm.sample();
    cg_ebreak_execute_without_ebreakm.sample();
    cg_cebreak_execute_without_ebreakm.sample();
    cg_trigger_match.sample();
    cg_trigger_match_disabled.sample();
    cg_debug_mode_exception.sample();
    cg_debug_mode_ecall.sample();
    cg_irq_in_debug.sample();
    cg_wfi_in_debug.sample();
    cg_wfi_debug_req.sample();
    cg_single_step.sample();
    cg_mmode_dret.sample();
    cg_irq_dreq.sample();
    cg_debug_regs.sample();
    cg_trigger_regs.sample();
    cg_counters_enabled.sample();
  end
endtask  : sample_clk_i
