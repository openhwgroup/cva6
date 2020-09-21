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
    input        ecall_insn_i,

    // Debug signals
    input              debug_req_i, // From controller
    input              debug_mode_q, // From controller
    input logic [31:0] dcsr_q, // From controller
    input logic [31:0] depc_q, // From cs regs
    input logic [31:0] dm_halt_addr_i,
    input logic [31:0] dm_exception_addr_i,

    input logic [31:0] mcause_q,
    input logic [31:0] mtvec,
    input logic [31:0] mepc_q,

    input [31:0] tdata1,
    input [31:0] tdata2,
    input trigger_match_i,
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

    // cover that we hit pc==tdata2 without having enabled trigger in m-mode
    covergroup cg_trigger_match_disabled @(posedge clk_i);
        option.per_instance = 1;
        dis : coverpoint tdata1[2] {
            bins hit = {0};
        }
        match: coverpoint addr_match {
           bins hit = {1};
        }
        mmode : coverpoint debug_mode_q {
           bins hit = {0};
        }
        match_without_en : cross dis, match, mmode;
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
        stepie : coverpoint dcsr_q[11];
        mmode_step : cross step, mmode;
        mmode_step_trigger_match : cross step, mmode, trigger;
        mmode_step_wfi : cross step, mmode, wfi;
        mmode_step_stepie : cross step, mmode, stepie;
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
        addr  : coverpoint id_stage_instr_rdata_i[31:20]{ // csr addr not updated if illegal access
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
        $rose(debug_req_i) |-> ##[1:6] (debug_mode_q && (dcsr_q[8:6]=== cv32e40p_pkg::DBG_CAUSE_HALTREQ) && 
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
        in_wfi && debug_req_i |=> !core_sleep_o ##5 debug_mode_q; 
    endproperty

    a_sleep_debug_req : assert property(p_sleep_debug_req)
        else
            `uvm_error(info_tag, $sformatf("Did not exit sleep after debug_req_i"));
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
    assign is_wfi = id_stage_instr_valid_i &
                  ((id_stage_instr_rdata_i & WFI_INSTR_MASK) == WFI_INSTR_DATA);
    assign pending_enabled_irq = irq_i & mie_q;
    assign is_dret = id_stage_instr_valid_i & (id_stage_instr_rdata_i == 32'h7B200073);
endmodule : uvmt_cv32e40p_debug_assert
