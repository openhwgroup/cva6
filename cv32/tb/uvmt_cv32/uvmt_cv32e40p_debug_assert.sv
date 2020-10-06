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
      uvmt_cv32_debug_cov_assert_if cov_assert_if
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
  logic [31:0] pc_at_dbg_req; // Capture PC when debug_req_i or ebreak is active
  logic [31:0] pc_at_ebreak; // Capture PC when ebreak
  logic [31:0] halt_addr_at_entry;
  logic [31:0] exception_addr_at_entry;
  
  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge cov_assert_if.clk_i); endclocking
  default disable iff !(cov_assert_if.rst_ni);
  
  assign cov_assert_if.is_ebreak = cov_assert_if.is_decoding & 
                                   cov_assert_if.id_stage_instr_valid_i &
                     (cov_assert_if.id_stage_instr_rdata_i == 32'h00100073) & 
                     cov_assert_if.id_stage_is_compressed == 1'b0;

  assign cov_assert_if.is_cebreak = cov_assert_if.is_decoding &
                                    cov_assert_if.id_stage_instr_valid_i &
                     (cov_assert_if.id_stage_instr_rdata_i == 32'h00100073) & 
                     cov_assert_if.id_stage_is_compressed == 1'b1;

    // ---------------------------------------
    // Assertions
    // ---------------------------------------

    // debug_req_i results in debug mode
    // TBD: Is there a fixed latency for this?
    // Only check when instr_valid_i is high, as debug_req is only evaluated
    // in decode with a valid instruction
    // Exclude ebreak and trigger as these have higher priority
    property p_debug_mode_ext_req;
        cov_assert_if.debug_req_i && cov_assert_if.id_stage_instr_valid_i && cov_assert_if.is_decoding && !cov_assert_if.debug_mode_q &&
        !cov_assert_if.trigger_match_i && !cov_assert_if.is_ebreak && !cov_assert_if.is_cebreak      
        |-> ##[1:40] (cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6]=== cv32e40p_pkg::DBG_CAUSE_HALTREQ) && 
                                                        (cov_assert_if.depc_q == pc_at_dbg_req)) &&
                                                        (cov_assert_if.id_stage_pc == halt_addr_at_entry);
    endproperty   

    a_debug_mode_ext_req: assert property(p_debug_mode_ext_req)
        else
            `uvm_error(info_tag, $sformatf("Debug mode not entered following debug_req_i or wrong cause. Cause=%d",cov_assert_if.dcsr_q[8:6]));


    // c.ebreak with dcsr.ebreakm results in debug mode
    property p_cebreak_debug_mode;
        $rose(cov_assert_if.is_cebreak) && cov_assert_if.dcsr_q[15] == 1'b1 && !cov_assert_if.debug_mode_q && cov_assert_if.id_valid|-> ##[1:40] cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6] === cv32e40p_pkg::DBG_CAUSE_EBREAK) &&
                                                            (cov_assert_if.depc_q == pc_at_dbg_req) &&
                                                            (cov_assert_if.id_stage_pc == halt_addr_at_entry);
    endproperty

    a_cebreak_debug_mode: assert property(p_cebreak_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not entered following c.ebreak with dcsr.ebreakm or wrong cause. Cause=%d",cov_assert_if.dcsr_q[8:6]));

    // ebreak with dcsr.ebreakm results in debug mode
    property p_ebreak_debug_mode;
        $rose(cov_assert_if.is_ebreak) && cov_assert_if.dcsr_q[15] == 1'b1 && !cov_assert_if.debug_mode_q && cov_assert_if.id_valid|-> ##[1:40] cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6] === cv32e40p_pkg::DBG_CAUSE_EBREAK) &&
                                                            (cov_assert_if.depc_q == pc_at_dbg_req) &&
                                                            (cov_assert_if.id_stage_pc == halt_addr_at_entry);
    endproperty

    a_ebreak_debug_mode: assert property(p_ebreak_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not entered following ebreak with dcsr.ebreakm or wrong cause. Cause=%d",cov_assert_if.dcsr_q[8:6]));


    // c.ebreak without dcsr.ebreakm results in exception at mtvec
    property p_cebreak_exception;
        $rose(cov_assert_if.is_cebreak) && cov_assert_if.dcsr_q[15] == 1'b0 && !cov_assert_if.debug_mode_q  && cov_assert_if.is_decoding && cov_assert_if.id_valid|-> ##[1:40] !cov_assert_if.debug_mode_q && (cov_assert_if.mcause_q[5:0] === cv32e40p_pkg::EXC_CAUSE_BREAKPOINT) &&
                                                                             (cov_assert_if.mepc_q == pc_at_ebreak) &&
                                                                             (cov_assert_if.id_stage_pc == cov_assert_if.mtvec);
    endproperty
    
    a_cebreak_exception: assert property(p_cebreak_exception)
        else
            `uvm_error(info_tag,$sformatf("Exception not entered correctly after ebreak with dcsr.ebreak=0"));

    // c.ebreak during debug mode results in relaunch of debug mode
    property p_cebreak_during_debug_mode;
        $rose(cov_assert_if.is_cebreak) ##0 cov_assert_if.debug_mode_q  && cov_assert_if.id_valid |-> ##[1:40] cov_assert_if.debug_mode_q  &&
                                                       (cov_assert_if.id_stage_pc == halt_addr_at_entry); // TODO should check no change in dpc and dcsr
    endproperty

    a_cebreak_during_debug_mode: assert property(p_cebreak_during_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not restarted after c.ebreak"));

    // ebreak during debug mode results in relaunch
    property p_ebreak_during_debug_mode;
        $rose(cov_assert_if.is_ebreak) ##0 cov_assert_if.debug_mode_q && cov_assert_if.id_valid |-> ##[1:40] cov_assert_if.debug_mode_q && 
                                                     (cov_assert_if.id_stage_pc == halt_addr_at_entry); // TODO should check no change in dpc and dcsr
    endproperty

    a_ebreak_during_debug_mode: assert property(p_ebreak_during_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not restarted after ebreak"));

    // Trigger match results in debug mode
    property p_trigger_match;
        cov_assert_if.trigger_match_i ##0 cov_assert_if.tdata1[2] ##0 !cov_assert_if.debug_mode_q ##0 cov_assert_if.id_stage_instr_valid_i ##0 cov_assert_if.is_decoding
        |-> ##[1:40] (cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6]=== cv32e40p_pkg::DBG_CAUSE_TRIGGER) && 
                                                            (cov_assert_if.depc_q == cov_assert_if.tdata2)) &&
                                                            (cov_assert_if.id_stage_pc == halt_addr_at_entry);
    endproperty   

    a_trigger_match: assert property(p_trigger_match)
        else
            `uvm_error(info_tag, $sformatf("Debug mode not correctly entered after trigger match depc=%08x,  tdata2=%08x", cov_assert_if.depc_q, cov_assert_if.tdata2)); 

    // Address match without trigger enabled should NOT result in debug mode
    property p_trigger_match_disabled;
        $rose(cov_assert_if.addr_match) && !cov_assert_if.debug_mode_q |-> ##[1:6] !cov_assert_if.debug_mode_q;
    endproperty

    a_trigger_match_disabled: assert property(p_trigger_match_disabled)
        else
            `uvm_error(info_tag, "Trigger match with tdata[2]==0 resulted in debug mode");

    // Exception in debug mode results in pc->dm_exception_addr_i
    property p_debug_mode_exception;
        $rose(cov_assert_if.illegal_insn_i) && cov_assert_if.debug_mode_q && cov_assert_if.is_decoding && cov_assert_if.id_valid |-> ##[1:40] cov_assert_if.debug_mode_q && (cov_assert_if.id_stage_pc == exception_addr_at_entry);
    endproperty

    a_debug_mode_exception : assert property(p_debug_mode_exception)
        else
            `uvm_error(info_tag, $sformatf("Exception in debug mode not handled incorrectly. dm=%d, pc=%08x", cov_assert_if.debug_mode_q, cov_assert_if.id_stage_pc));

    // ECALL in debug mode results in pc->dm_exception_addr_i
    property p_debug_mode_ecall;
        $rose(cov_assert_if.ecall_insn_i) && cov_assert_if.debug_mode_q  && cov_assert_if.is_decoding && cov_assert_if.id_valid 
        |-> ##[1:6] cov_assert_if.debug_mode_q && (cov_assert_if.id_stage_pc == exception_addr_at_entry);
    endproperty

    a_debug_mode_ecall : assert property(p_debug_mode_ecall)
        else
            `uvm_error(info_tag, $sformatf("ECALL in debug mode not handled incorrectly. dm=%d, pc=%08x", cov_assert_if.debug_mode_q, cov_assert_if.id_stage_pc));

    // IRQ in debug mode are masked
    property p_irq_in_debug;
        cov_assert_if.debug_mode_q |-> !cov_assert_if.irq_ack_o;
    endproperty

    a_irq_in_debug : assert property(p_irq_in_debug)
        else
            `uvm_error(info_tag, $sformatf("IRQ not ignored while in debug mode"));

    // WFI in debug mode does not sleep
    property p_wfi_in_debug;
        cov_assert_if.debug_mode_q && $rose(cov_assert_if.is_wfi) |-> ##6 !cov_assert_if.core_sleep_o;
    endproperty

    a_wfi_in_debug : assert property(p_wfi_in_debug)
        else
            `uvm_error(info_tag, $sformatf("WFI in debug mode cause core_sleep_o=1"));

    // Debug request while sleeping makes core wake up and enter debug mode
    property p_sleep_debug_req;
        cov_assert_if.in_wfi && cov_assert_if.debug_req_i |=> !cov_assert_if.core_sleep_o ##[0:40] cov_assert_if.debug_mode_q; 
    endproperty

    a_sleep_debug_req : assert property(p_sleep_debug_req)
        else
            `uvm_error(info_tag, $sformatf("Did not exit sleep(== %d) after debug_req_i. Debug_mode = %d", cov_assert_if.core_sleep_o, cov_assert_if.debug_mode_q));

    // Accessing debug regs in m-mode is illegal
    property p_debug_regs_mmode;
        cov_assert_if.csr_access && !cov_assert_if.debug_mode_q && cov_assert_if.id_stage_instr_rdata_i[31:20] inside {'h7B0, 'h7B1, 'h7B2, 'h7B3} |->
                 cov_assert_if.illegal_insn_i; 
    endproperty

    a_debug_regs_mmode : assert property(p_debug_regs_mmode)
        else
            `uvm_error(info_tag, "Accessing debug regs in M-mode did not result in illegal instruction");

    // Exception while single step -> PC is set to exception handler before
    // debug
    property p_single_step_exception;
        !cov_assert_if.debug_mode_q && cov_assert_if.dcsr_q[2] && cov_assert_if.illegal_insn_q |-> ##[1:20] cov_assert_if.debug_mode_q && (cov_assert_if.depc_q == cov_assert_if.mtvec);
    endproperty

    a_single_step_exception : assert property(p_single_step_exception)
        else
            `uvm_error(info_tag, "PC not set to exception handler after single step with exception");

    // Trigger during single step 
    property p_single_step_trigger;
        !cov_assert_if.debug_mode_q && cov_assert_if.dcsr_q[2] && cov_assert_if.addr_match && cov_assert_if.tdata1[2] && cov_assert_if.id_stage_instr_valid_i|->
                ##[1:20] cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6] == cv32e40p_pkg::DBG_CAUSE_TRIGGER) && (cov_assert_if.depc_q == pc_at_dbg_req);
    endproperty

    a_single_step_trigger : assert property (p_single_step_trigger)
        else
            `uvm_error(info_tag, $sformatf("Single step and trigger error: depc = %08x, cause = %d",cov_assert_if.depc_q, cov_assert_if.dcsr_q[8:6]));

    // Single step WFI must not result in sleeping
    property p_single_step_wfi;
        !cov_assert_if.debug_mode_q && cov_assert_if.dcsr_q[2] && cov_assert_if.is_wfi |->
                ##[1:20] cov_assert_if.debug_mode_q && !cov_assert_if.core_sleep_o;
    endproperty

    a_single_step_wfi : assert property(p_single_step_wfi)
        else
            `uvm_error(info_tag, "Debug mode not entered after single step WFI or core went sleeping");

    // dret in M-mode will cause illegal instruction
    property p_mmode_dret;
        !cov_assert_if.debug_mode_q && cov_assert_if.is_dret |-> ##1 cov_assert_if.illegal_insn_q;
    endproperty

    a_mmode_dret : assert property(p_mmode_dret)
        else
            `uvm_error(info_tag, "Executing dret in M-mode did not result in illegal instruction");

    // dret in D-mode will restore pc and exit D-mode
    property p_dmode_dret;
        cov_assert_if.debug_mode_q && cov_assert_if.is_dret |-> ##[1:6] !cov_assert_if.debug_mode_q && (cov_assert_if.id_stage_pc == cov_assert_if.depc_q);
    endproperty

    a_dmode_dret : assert property(p_dmode_dret)
        else
            `uvm_error(info_tag, "Dret did not cause correct return from debug mode");

    // Check that trigger regs cannot be written from M-mode
    // TSEL, and TDATA3 are tied to zero, hence no register to check 
    property p_mmode_tdata1_write;
        !cov_assert_if.debug_mode_q && cov_assert_if.csr_access && cov_assert_if.csr_op == 'h1 && cov_assert_if.id_stage_instr_rdata_i[31:20] == 'h7A1 |-> ##2 $stable(cov_assert_if.tdata1);
    endproperty

    a_mmode_tdata1_write : assert property(p_mmode_tdata1_write)
        else
            `uvm_error(info_tag, "Writing tdata1 from M-mode not allowed to change register value!");

  property p_mmode_tdata2_write;
        !cov_assert_if.debug_mode_q && cov_assert_if.csr_access && cov_assert_if.csr_op == 'h1 && cov_assert_if.id_stage_instr_rdata_i[31:20] == 'h7A2 |-> ##2 $stable(cov_assert_if.tdata2);
    endproperty

    a_mmode_tdata2_write : assert property(p_mmode_tdata2_write)
        else
            `uvm_error(info_tag, "Writing tdata2 from M-mode not allowed to change register value!");

    // Check that mcycle works as expected when not sleeping
    property p_mcycle_count;
        !cov_assert_if.mcountinhibit_q[0] && !cov_assert_if.core_sleep_o |=>  (cov_assert_if.mcycle == ($past(cov_assert_if.mcycle)+1));
    endproperty

    a_mcycle_count : assert property(p_mcycle_count)
        else
            `uvm_error(info_tag, "Mcycle not counting when mcountinhibit[0] is cleared!");

    // Check that minstret works as expected when not sleeping
    property p_minstret_count;
        !cov_assert_if.mcountinhibit_q[2] && cov_assert_if.inst_ret && !cov_assert_if.core_sleep_o |=> (cov_assert_if.minstret == ($past(cov_assert_if.minstret)+1));
    endproperty

    a_minstret_count : assert property(p_minstret_count)
        else
            `uvm_error(info_tag, "Minstret not counting when mcountinhibit[2] is cleared!");

// -------------------------------------------
    // Capture internal states for use in checking
    // -------------------------------------------
    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if(!cov_assert_if.rst_ni) begin
            pc_at_dbg_req <= 32'h0;
            pc_at_ebreak <= 32'h0;
        end else begin
            // Capture debug pc
            if(cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_ID) begin
                pc_at_dbg_req <= cov_assert_if.id_stage_pc;
            end else if(cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_IF) begin
                pc_at_dbg_req <= cov_assert_if.if_stage_pc;
            end

            // Capture pc at ebreak
            if(cov_assert_if.is_ebreak || cov_assert_if.is_cebreak ) begin
                pc_at_ebreak <= cov_assert_if.id_stage_pc;
            end
       end
    end        

    // Keep track of wfi state
    always @(posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
    if (!cov_assert_if.rst_ni) begin
      cov_assert_if.in_wfi <= 1'b0;
    end
    else begin
      if (cov_assert_if.is_wfi && !cov_assert_if.debug_mode_q && cov_assert_if.id_valid && cov_assert_if.is_decoding)
        cov_assert_if.in_wfi <= 1'b1;
      else if (cov_assert_if.pending_enabled_irq || cov_assert_if.debug_req_i)
        cov_assert_if.in_wfi <= 1'b0;
    end
  end

  // Capture dm_halt_addr_i value
  always@ (posedge cov_assert_if.clk_i) begin
      if(cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_ID)
          halt_addr_at_entry <= {cov_assert_if.dm_halt_addr_i[31:2], 2'b00};
  end
  always@ (posedge cov_assert_if.clk_i)  begin
      if((cov_assert_if.illegal_insn_i | cov_assert_if.ecall_insn_i) & cov_assert_if.pc_set & cov_assert_if.debug_mode_q)
          exception_addr_at_entry = {cov_assert_if.dm_exception_addr_i[31:2], 2'b00};
  end

    assign cov_assert_if.addr_match   = (cov_assert_if.id_stage_pc == cov_assert_if.tdata2);
    assign cov_assert_if.dpc_will_hit = (cov_assert_if.depc_n == cov_assert_if.tdata2);
    assign cov_assert_if.is_wfi = cov_assert_if.id_stage_instr_valid_i &
                                  ((cov_assert_if.id_stage_instr_rdata_i & WFI_INSTR_MASK) == WFI_INSTR_DATA);
    assign cov_assert_if.pending_enabled_irq = cov_assert_if.irq_i & cov_assert_if.mie_q;
    assign cov_assert_if.is_dret             = cov_assert_if.id_valid & cov_assert_if.is_decoding & (cov_assert_if.id_stage_instr_rdata_i == 32'h7B200073);
endmodule : uvmt_cv32e40p_debug_assert
