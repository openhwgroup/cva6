//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
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

module uvmt_cv32e40p_debug_assert  
  import uvm_pkg::*;
  import cv32e40p_pkg::*;
  (
    
    input clk_i,
    input rst_ni,

    // Core inputs
    input        fetch_enable_i, // external core fetch enable

    // External interrupt interface
    input [31:0] irq_i,
    input        irq_ack_o,
    input [4:0]  irq_id_o,
    input [31:0] mie_q,

    // Instruction fetch stage
    input        if_stage_instr_rvalid_i, // Instruction word is valid
    input [31:0] if_stage_instr_rdata_i, // Instruction word data

    // Instruction ID stage (determines executed instructions)  
    input        id_stage_instr_valid_i, // instruction word is valid
    input [31:0] id_stage_instr_rdata_i, // Instruction word data
    input        id_stage_is_compressed,
    input [31:0] id_stage_pc, // Program counter in decode
    input [31:0] if_stage_pc, // Program counter in fetch
    input ctrl_state_e  ctrl_fsm_cs,            // Controller FSM states with debug_req
    input        illegal_insn_i,
    input        illegal_insn_q, // output from controller
    input        ecall_insn_i,

    // Debug signals
    input              debug_req_i, // From controller
    input              debug_mode_q, // From controller
    input logic [31:0] dcsr_q, // From controller
    input logic [31:0] depc_q, // From cs regs
    input logic [31:0] depc_n, // 
    input logic [31:0] dm_halt_addr_i,
    input logic [31:0] dm_exception_addr_i,

    input logic [31:0] mcause_q,
    input logic [31:0] mtvec,
    input logic [31:0] mepc_q,

    input [31:0] tdata1,
    input [31:0] tdata2,
    input trigger_match_i,

    // Counter related input from cs_registers
    input logic [31:0] mcountinhibit_q,
    input logic [63:0] mcycle,
    input logic [63:0] minstret,
    input logic inst_ret,
    // WFI Interface
    input core_sleep_o,

    input logic csr_access,
    input logic [1:0] csr_op,
    input logic [11:0] csr_addr
  );

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------  
    localparam WFI_INSTR_MASK = 32'hffffffff;
    localparam WFI_INSTR_DATA = 32'h10500073;
  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "CV32E40P_DEBUG_ASSERT";
 
  logic is_ebreak; // compiler cannot generate uncompressed ebreak yet(?)
  logic is_cebreak;
  logic is_wfi;
  logic in_wfi;
  logic is_dret;
  logic [31:0] pc_at_dbg_req; // Capture PC when debug_req_i or ebreak is active
  logic [31:0] pc_at_ebreak; // Capture PC when ebreak

  // check addr match locally for checking with matching disabled
  logic addr_match;

  // Check that value in dpc will match trigger address
  logic dpc_will_hit;
  // We need irq signals to properly track wfi/sleep
  logic [31:0] pending_enabled_irq;
    
  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge clk_i); endclocking
  default disable iff !(rst_ni);

  // ---------------------------------------------------------------------------
  // covergroups
  // ---------------------------------------------------------------------------

  // Cover which fsm states are active when debug_req is asserted
  covergroup cg_debug_mode_ext @(posedge debug_req_i);
          option.per_instance = 1;
          state: coverpoint ctrl_fsm_cs {
                  bins valid_states[] = { [ctrl_fsm_cs.first:ctrl_fsm_cs.last]}; 
          }
  endgroup

  // Cover that we execute ebreak with dcsr.ebreakm==1
  covergroup cg_ebreak_execute_with_ebreakm @(posedge clk_i);
          option.per_instance = 1;
          ex: coverpoint is_ebreak {
                  bins active = {1};
          }
          ebreakm_set: coverpoint dcsr_q[15] {
                  bins active = {1};
          }
          dm : coverpoint debug_mode_q {
                  bins active = {1};
          }
          ebreak_with_ebreakm: cross ex, ebreakm_set;  
          ebreak_in_debug : cross ex, dm;
  endgroup
    
  // Cover that we execute c.ebreak with dcsr.ebreakm==1
  covergroup cg_cebreak_execute_with_ebreakm @(posedge clk_i);
          option.per_instance = 1;
          ex: coverpoint is_cebreak {
                  bins active = {1};
          }
          ebreakm_set: coverpoint dcsr_q[15] {
                  bins active = {1};
          }
          dm : coverpoint debug_mode_q {
                  bins active = {1};
          }
          cebreak_with_ebreakm: cross ex, ebreakm_set;  
          cebreak_in_debug : cross ex, dm;
  endgroup

  // Cover that we execute ebreak with dcsr.ebreakm==0
  covergroup cg_ebreak_execute_without_ebreakm @(posedge clk_i);
          option.per_instance = 1;
          ex: coverpoint is_ebreak {
                  bins active = {1};
          }
          ebreakm_clear: coverpoint dcsr_q[15] {
                  bins active = {0};
          }
          test: cross ex, ebreakm_clear;  
  endgroup
    
  // Cover that we execute c.ebreak with dcsr.ebreakm==0
  covergroup cg_cebreak_execute_without_ebreakm @(posedge clk_i);
          option.per_instance = 1;
          ex: coverpoint is_cebreak {
                  bins active = {1};
          }
          ebreakm_clear: coverpoint dcsr_q[15] {
                  bins active = {0};
          }
          test: cross ex, ebreakm_clear;  
  endgroup

    // TODO: Implement covergroup for ebreak+dcsr.ebreakm when executing an
    // exception
    //

    // Cover that we hit a trigger match
    covergroup cg_trigger_match @(posedge clk_i);
        option.per_instance = 1;
        en : coverpoint tdata1[2] {
            bins active = {1};
        }
        match: coverpoint trigger_match_i {
            bins hit = {1};
        }
        ok_match: cross en, match;
    endgroup

    // cover that we hit pc==tdata2  without having enabled trigger in m/d-mode
    // cover hit in d-mode with trigger enabled (no action)
    covergroup cg_trigger_match_disabled @(posedge clk_i);
        option.per_instance = 1;
        dis : coverpoint tdata1[2] {
            bins hit = {0};
        }
        en : coverpoint tdata1[2] {
            bins hit = {1};
        }
        match: coverpoint addr_match {
           bins hit = {1};
        }
        mmode : coverpoint debug_mode_q {
           bins m = {0};
        }
        dmode : coverpoint debug_mode_q {
           bins m = {1};
        }
        m_match_without_en : cross dis, match, mmode;
        d_match_without_en : cross dis, match, dmode;
        d_match_with_en    : cross en, match, dmode;
    endgroup


    // Cover that we hit an exception during debug mode
    covergroup cg_debug_mode_exception @(posedge clk_i);
        option.per_instance = 1;
        dm : coverpoint debug_mode_q {
            bins hit  = {1};
        }
        ill : coverpoint illegal_insn_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, ill;
    endgroup

    // Cover that we hit an ecall during debug mode
    covergroup cg_debug_mode_ecall @(posedge clk_i);
        option.per_instance = 1;
        dm : coverpoint debug_mode_q {
            bins hit  = {1};
        }
        ill : coverpoint ecall_insn_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, ill;
    endgroup

    // Cover that we get interrupts while in debug mode
    covergroup cg_irq_in_debug @(posedge clk_i);
        option.per_instance = 1;
        dm : coverpoint debug_mode_q {
            bins hit  = {1};
        }
        irq : coverpoint |irq_i {
            bins hit = {1};
        }
        ex_in_debug : cross dm, irq;
    endgroup

    // Cover that hit a WFI insn in debug mode
    covergroup cg_wfi_in_debug @(posedge clk_i);
        option.per_instance = 1;
        iswfi : coverpoint is_wfi {
                bins hit  = {1};
        }
        dm : coverpoint debug_mode_q {
            bins hit = {1};
        }
        dm_wfi : cross iswfi, dm;
    endgroup

    // Cover that we get a debug_req while in wfi
    covergroup cg_wfi_debug_req @(posedge clk_i);
        option.per_instance = 1;
        inwfi : coverpoint in_wfi {
                bins hit  = {1};
        }
        dreq: coverpoint debug_req_i {
            bins hit = {1};
        }
        dm_wfi : cross inwfi, dreq;
    endgroup

    // Cover that we perform single stepping
    covergroup cg_single_step @(posedge clk_i);
        option.per_instance = 1;
        step : coverpoint dcsr_q[2] {
                bins en  = {1};
        }
        mmode: coverpoint debug_mode_q {
            bins hit = {0};
        }
        trigger : coverpoint trigger_match_i {
            bins hit = {1};
        }
        wfi : coverpoint is_wfi {
            bins hit = {1};
        }
        ill : coverpoint illegal_insn_i {
            bins hit = {1};
        }
        pc_will_trig : coverpoint dpc_will_hit {
            bins hit = {1};
        } 
        stepie : coverpoint dcsr_q[11];
        mmode_step : cross step, mmode;
        mmode_step_trigger_match : cross step, mmode, trigger;
        mmode_step_wfi : cross step, mmode, wfi;
        mmode_step_stepie : cross step, mmode, stepie;
        mmode_step_illegal : cross step, mmode, ill;
        mmode_step_next_pc_will_match : cross step, mmode, pc_will_trig;
    endgroup

    // Cover dret is executed in machine mode
    covergroup cg_mmode_dret @(posedge clk_i);
        option.per_instance = 1;
        mmode : coverpoint debug_mode_q;
        dret_ins : coverpoint is_dret {
            bins hit = {1};
        }
        dret_ex : cross mmode, dret_ins;
    endgroup

    // Cover debug_req and irq asserted on same cycle
    covergroup cg_irq_dreq @(posedge clk_i);
        option.per_instance = 1;
        dreq : coverpoint $rose(debug_req_i);
        irq  : coverpoint $rose(|irq_i);
        irq_and_dreq : cross dreq, irq;
    endgroup

    // Cover access to dcsr, dpc and dscratch0/1
    // Do we need to cover all READ/WRITE/SET/CLEAR from m-mode?
    covergroup cg_debug_regs @(posedge clk_i);
        option.per_instance = 1;
        mode : coverpoint debug_mode_q; // Only M and D supported
        access : coverpoint csr_access {
            bins hit = {1};
        }
        op : coverpoint csr_op {
            bins read = {'h0};
            bins write = {'h1};
        }
        addr  : coverpoint id_stage_instr_rdata_i[31:20] { // csr addr not updated if illegal access
            bins dcsr = {'h7B0};
            bins dpc = {'h7B1};
            bins dscratch0 = {'h7B2};
            bins dscratch1 = {'h7B3};
        }
        dregs_access : cross mode, access, op,addr;
    endgroup

    // Cover access to trigger registers
    // Do we need to cover all READ/WRITE/SET/CLEAR from m-mode?
    covergroup cg_trigger_regs @(posedge clk_i);
        option.per_instance = 1;
        mode : coverpoint debug_mode_q; // Only M and D supported
        access : coverpoint csr_access {
            bins hit = {1};
        }
        op : coverpoint csr_op {
            bins read = {'h0};
            bins write = {'h1};
        }
        addr  : coverpoint id_stage_instr_rdata_i[31:20]{ // csr addr not updated if illegal access
            bins tsel = {'h7A0};
            bins tdata1 = {'h7A1};
            bins tdata2 = {'h7A2};
            bins tdata3 = {'h7A3};
            bins tinfo = {'h7A4};
        }
        tregs_access : cross mode, access, op,addr;
    endgroup

    // Cover that we run with counters mcycle and minstret enabled
    covergroup cg_counters_enabled @(posedge clk_i);
        option.per_instance = 1;
        mcycle_en : coverpoint mcountinhibit_q[0];
        minstret_en : coverpoint mcountinhibit_q[2];
    endgroup
// cg instances
  cg_debug_mode_ext cg_debug_mode_i;
  cg_ebreak_execute_with_ebreakm cg_ebreak_execute_with_ebreakm_i;
  cg_cebreak_execute_with_ebreakm cg_cebreak_execute_with_ebreakm_i;
  cg_ebreak_execute_without_ebreakm cg_ebreak_execute_without_ebreakm_i;
  cg_cebreak_execute_without_ebreakm cg_cebreak_execute_without_ebreakm_i;
  cg_trigger_match cg_trigger_match_i;
  cg_trigger_match_disabled cg_trigger_match_disabled_i;
  cg_debug_mode_exception cg_debug_mode_exception_i;
  cg_debug_mode_ecall cg_debug_mode_ecall_i;
  cg_irq_in_debug cg_irq_in_debug_i;
  cg_wfi_in_debug cg_wfi_in_debug_i;
  cg_wfi_debug_req cg_wfi_debug_req_i;
  cg_single_step cg_single_step_i;
  cg_mmode_dret cg_mmode_dret_i;
  cg_irq_dreq  cg_irq_dreq_i;
  cg_debug_regs cg_debug_regs_i;
  cg_trigger_regs cg_trigger_regs_i;
  cg_counters_enabled cg_counters_enabled_i;
  // create cg's at start of simulation
  initial begin
      cg_debug_mode_i = new();
      cg_ebreak_execute_with_ebreakm_i = new();
      cg_cebreak_execute_with_ebreakm_i = new();
      cg_ebreak_execute_without_ebreakm_i = new();
      cg_cebreak_execute_without_ebreakm_i = new();
      cg_trigger_match_i = new();
      cg_trigger_match_disabled_i = new();
      cg_debug_mode_exception_i = new();
      cg_debug_mode_ecall_i = new();
      cg_irq_in_debug_i = new();
      cg_wfi_in_debug_i = new();
      cg_wfi_debug_req_i = new();
      cg_single_step_i = new();
      cg_mmode_dret_i = new();
      cg_irq_dreq_i = new();
      cg_debug_regs_i = new();
      cg_trigger_regs_i = new();
      cg_counters_enabled_i = new();
  end         

  assign is_ebreak = id_stage_instr_valid_i & 
                     (id_stage_instr_rdata_i == 32'h00100073) & 
                     id_stage_is_compressed == 1'b0;

  assign is_cebreak = id_stage_instr_valid_i & 
                     (id_stage_instr_rdata_i == 32'h00100073) & 
                     id_stage_is_compressed == 1'b1;

    // ---------------------------------------
    // Assertions
    // ---------------------------------------

    // debug_req_i results in debug mode
    // TBD: Is there a fixed latency for this?
    property p_debug_mode_ext_req;
        $rose(debug_req_i) && !debug_mode_q |-> ##[1:40] (debug_mode_q && (dcsr_q[8:6]=== cv32e40p_pkg::DBG_CAUSE_HALTREQ) && 
                                                        (depc_q == pc_at_dbg_req)) &&
                                                        (id_stage_pc == dm_halt_addr_i);
    endproperty   

    a_debug_mode_ext_req: assert property(p_debug_mode_ext_req)
        else
            `uvm_error(info_tag, $sformatf("Debug mode not entered following debug_req_i or wrong cause. Cause=%d",dcsr_q[8:6]));


    // c.ebreak with dcsr.ebreakm results in debug mode
    property p_cebreak_debug_mode;
        $rose(is_cebreak) && dcsr_q[15] == 1'b1 |-> ##[1:6] debug_mode_q && (dcsr_q[8:6] === cv32e40p_pkg::DBG_CAUSE_EBREAK) &&
                                                            (depc_q == pc_at_dbg_req) &&
                                                            (id_stage_pc == dm_halt_addr_i);
    endproperty

    a_cebreak_debug_mode: assert property(p_cebreak_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not entered following c.ebreak with dcsr.ebreakm or wrong cause. Cause=%d",dcsr_q[8:6]));

    // ebreak with dcsr.ebreakm results in debug mode
    property p_ebreak_debug_mode;
        $rose(is_ebreak) && dcsr_q[15] == 1'b1 |-> ##[1:6] debug_mode_q && (dcsr_q[8:6] === cv32e40p_pkg::DBG_CAUSE_EBREAK) &&
                                                            (depc_q == pc_at_dbg_req) &&
                                                            (id_stage_pc == dm_halt_addr_i);
    endproperty

    a_ebreak_debug_mode: assert property(p_ebreak_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not entered following ebreak with dcsr.ebreakm or wrong cause. Cause=%d",dcsr_q[8:6]));


    // c.ebreak without dcsr.ebreakm results in exception at mtvec
    property p_cebreak_exception;
        $rose(is_cebreak) && dcsr_q[15] == 1'b0 && !debug_mode_q |-> ##[1:6] !debug_mode_q && (mcause_q[5:0] === cv32e40p_pkg::EXC_CAUSE_BREAKPOINT) &&
                                                                             (mepc_q == pc_at_ebreak) &&
                                                                             (id_stage_pc == mtvec);
    endproperty
    
    a_cebreak_exception: assert property(p_cebreak_exception)
        else
            `uvm_error(info_tag,$sformatf("Exception not entered correctly after ebreak with dcsr.ebreak=0"));

    // c.ebreak during debug mode results in relaunch of debug mode
    property p_cebreak_during_debug_mode;
        $rose(is_cebreak) && debug_mode_q  |-> ##[1:6] debug_mode_q  &&
                                                       (id_stage_pc == dm_halt_addr_i); // TODO should check no change in dpc and dcsr
    endproperty

    a_cebreak_during_debug_mode: assert property(p_cebreak_during_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not restarted after c.ebreak"));

    // ebreak during debug mode results in relaunch
    property p_ebreak_during_debug_mode;
        $rose(is_ebreak) && debug_mode_q |-> ##[1:6] debug_mode_q && 
                                                     (id_stage_pc == dm_halt_addr_i); // TODO should check no change in dpc and dcsr
    endproperty

    a_ebreak_during_debug_mode: assert property(p_ebreak_during_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not restarted after ebreak"));

    // Trigger match results in debug mode
    property p_trigger_match;
        $rose(trigger_match_i) && debug_mode_q==1'b0 |-> ##[1:6] (debug_mode_q && (dcsr_q[8:6]=== cv32e40p_pkg::DBG_CAUSE_TRIGGER) && 
                                                            (depc_q == tdata2)) &&
                                                            (id_stage_pc == dm_halt_addr_i);
    endproperty   

    a_trigger_match: assert property(p_trigger_match)
        else
            `uvm_error(info_tag, $sformatf("Debug mode not correctly entered after trigger match depc=%08x,  tdata2=%08x", depc_q, tdata2)); 

    // Address match without trigger enabled should NOT result in debug mode
    property p_trigger_match_disabled;
        $rose(addr_match) && !debug_mode_q |-> ##[1:6] !debug_mode_q;
    endproperty

    a_trigger_match_disabled: assert property(p_trigger_match_disabled)
        else
            `uvm_error(info_tag, "Trigger match with tdata[2]==0 resulted in debug mode");

    // Exception in debug mode results in pc->dm_exception_addr_i
    property p_debug_mode_exception;
        $rose(illegal_insn_i) && debug_mode_q |-> ##[1:6] debug_mode_q && (id_stage_pc == dm_exception_addr_i);
    endproperty

    a_debug_mode_exception : assert property(p_debug_mode_exception)
        else
            `uvm_error(info_tag, $sformatf("Exception in debug mode not handled incorrectly. dm=%d, pc=%08x", debug_mode_q, id_stage_pc));

    // ECALL in debug mode results in pc->dm_exception_addr_i
    property p_debug_mode_ecall;
        $rose(ecall_insn_i) && debug_mode_q |-> ##[1:6] debug_mode_q && (id_stage_pc == dm_exception_addr_i);
    endproperty

    a_debug_mode_ecall : assert property(p_debug_mode_ecall)
        else
            `uvm_error(info_tag, $sformatf("ECALL in debug mode not handled incorrectly. dm=%d, pc=%08x", debug_mode_q, id_stage_pc));

    // IRQ in debug mode are masked
    property p_irq_in_debug;
        debug_mode_q |-> !irq_ack_o;
    endproperty

    a_irq_in_debug : assert property(p_irq_in_debug)
        else
            `uvm_error(info_tag, $sformatf("IRQ not ignored while in debug mode"));

    // WFI in debug mode does not sleep
    property p_wfi_in_debug;
        debug_mode_q && $rose(is_wfi) |-> ##6 !core_sleep_o;
    endproperty

    a_wfi_in_debug : assert property(p_wfi_in_debug)
        else
            `uvm_error(info_tag, $sformatf("WFI in debug mode cause core_sleep_o=1"));

    // Debug request while sleeping makes core wake up and enter debug mode
    property p_sleep_debug_req;
        in_wfi && debug_req_i |=> !core_sleep_o ##6 debug_mode_q; 
    endproperty

    a_sleep_debug_req : assert property(p_sleep_debug_req)
        else
            `uvm_error(info_tag, $sformatf("Did not exit sleep(== %d) after debug_req_i. Debug_mode = %d", core_sleep_o, debug_mode_q));

    // Accessing debug regs in m-mode is illegal
    property p_debug_regs_mmode;
        csr_access && !debug_mode_q && id_stage_instr_rdata_i[31:20] inside {'h7B0, 'h7B1, 'h7B2, 'h7B3} |->
                 illegal_insn_i; 
    endproperty

    a_debug_regs_mmode : assert property(p_debug_regs_mmode)
        else
            `uvm_error(info_tag, "Accessing debug regs in M-mode did not result in illegal instruction");

    // Exception while single step -> PC is set to exception handler before
    // debug
    property p_single_step_exception;
        !debug_mode_q && dcsr_q[2] && illegal_insn_q |-> ##[1:20] debug_mode_q && (depc_q == mtvec);
    endproperty

    a_single_step_exception : assert property(p_single_step_exception)
        else
            `uvm_error(info_tag, "PC not set to exception handler after single step with exception");

    // Trigger during single step 
    property p_single_step_trigger;
        !debug_mode_q && dcsr_q[2] && addr_match && tdata1[2] |->
                ##[1:20] debug_mode_q && (dcsr_q[8:6] == cv32e40p_pkg::DBG_CAUSE_TRIGGER) && (depc_q == pc_at_dbg_req);
    endproperty

    a_single_step_trigger : assert property (p_single_step_trigger)
        else
            `uvm_error(info_tag, $sformatf("Single step and trigger error: depc = %08x, cause = %d",depc_q, dcsr_q[8:6]));

    // Single step WFI must not result in sleeping
    property p_single_step_wfi;
        !debug_mode_q && dcsr_q[2] && is_wfi |->
                ##[1:20] debug_mode_q && !core_sleep_o;
    endproperty

    a_single_step_wfi : assert property(p_single_step_wfi)
        else
            `uvm_error(info_tag, "Debug mode not entered after single step WFI or core went sleeping");

    // dret in M-mode will cause illegal instruction
    property p_mmode_dret;
        !debug_mode_q && is_dret |-> ##1 illegal_insn_q;
    endproperty

    a_mmode_dret : assert property(p_mmode_dret)
        else
            `uvm_error(info_tag, "Executing dret in M-mode did not result in illegal instruction");

    // dret in D-mode will restore pc and exit D-mode
    property p_dmode_dret;
        debug_mode_q && is_dret |-> ##[1:6] !debug_mode_q && (id_stage_pc == depc_q);
    endproperty

    a_dmode_dret : assert property(p_dmode_dret)
        else
            `uvm_error(info_tag, "Dret did not cause correct return from debug mode");

    // Check that trigger regs cannot be written from M-mode
    // TSEL, and TDATA3 are tied to zero, hence no register to check 
    property p_mmode_tdata1_write;
        !debug_mode_q && csr_access && csr_op == 'h1 && id_stage_instr_rdata_i[31:20] == 'h7A1 |-> ##2 $stable(tdata1);
    endproperty

    a_mmode_tdata1_write : assert property(p_mmode_tdata1_write)
        else
            `uvm_error(info_tag, "Writing tdata1 from M-mode not allowed to change register value!");

  property p_mmode_tdata2_write;
        !debug_mode_q && csr_access && csr_op == 'h1 && id_stage_instr_rdata_i[31:20] == 'h7A2 |-> ##2 $stable(tdata2);
    endproperty

    a_mmode_tdata2_write : assert property(p_mmode_tdata2_write)
        else
            `uvm_error(info_tag, "Writing tdata2 from M-mode not allowed to change register value!");

    // Check that mcycle works as expected when not sleeping
    property p_mcycle_count;
        !mcountinhibit_q[0] && !core_sleep_o |=> (mcycle == ($past(mcycle)+1));
    endproperty

    a_mcycle_count : assert property(p_mcycle_count)
        else
            `uvm_error(info_tag, "Mcycle not counting when mcountinhibit[0] is cleared!");

    // Check that minstret works as expected when not sleeping
    property p_minstret_count;
        !mcountinhibit_q[2] && inst_ret && !core_sleep_o |=> (minstret == ($past(minstret)+1));
    endproperty

    a_minstret_count : assert property(p_minstret_count)
        else
            `uvm_error(info_tag, "Minstret not counting when mcountinhibit[2] is cleared!");

// -------------------------------------------
    // Capture internal states for use in checking
    // -------------------------------------------
    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni) begin
            pc_at_dbg_req <= 32'h0;
            pc_at_ebreak <= 32'h0;
        end else begin
            // Capture debug pc
            if(ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_ID) begin
                pc_at_dbg_req <= id_stage_pc;
            end else if(ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_IF) begin
                pc_at_dbg_req <= if_stage_pc;
            end

            // Capture pc at ebreak
            if(is_ebreak || is_cebreak) begin
                pc_at_ebreak <= id_stage_pc;
            end
       end
    end        

    // Keep track of wfi state
    always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_wfi <= 1'b0;
    end
    else begin
      if (is_wfi) 
        in_wfi <= 1'b1;
      else if (|pending_enabled_irq || debug_req_i)
        in_wfi <= 1'b0;
    end
  end

    assign addr_match = (id_stage_pc == tdata2);
    assign dpc_will_hit = (depc_n == tdata2);
    assign is_wfi = id_stage_instr_valid_i &
                  ((id_stage_instr_rdata_i & WFI_INSTR_MASK) == WFI_INSTR_DATA);
    assign pending_enabled_irq = irq_i & mie_q;
    assign is_dret = id_stage_instr_valid_i & (id_stage_instr_rdata_i == 32'h7B200073);
endmodule : uvmt_cv32e40p_debug_assert
