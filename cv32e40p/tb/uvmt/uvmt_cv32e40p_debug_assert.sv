//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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
      uvmt_cv32e40p_debug_cov_assert_if cov_assert_if
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
  logic halt_addr_at_entry_flag;
  logic [31:0] exception_addr_at_entry;
  logic exception_addr_at_entry_flag;
  logic [31:0] tdata2_at_entry;
  // Locally track which debug cause should be used
  logic [2:0] debug_cause_pri;
  logic [31:0] boot_addr_at_entry;

  // Locally track pc in ID stage to detect first instruction of debug code
  logic [31:0] prev_id_pc;
  logic first_debug_ins_flag;
  logic first_debug_ins;
  logic decode_valid;
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

  assign cov_assert_if.is_mulhsu = cov_assert_if.is_decoding &
                                   cov_assert_if.id_stage_instr_valid_i & 
                                   cov_assert_if.id_stage_instr_rdata_i[31:25] == 7'h1 &
                                   cov_assert_if.id_stage_instr_rdata_i[14:12] == 3'b010 &
                                   cov_assert_if.id_stage_instr_rdata_i[6:0]   == 7'h33;


  assign decode_valid =  cov_assert_if.id_stage_instr_valid_i & cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DECODE;
    // ---------------------------------------
    // Assertions
    // ---------------------------------------

    // check that we enter debug mode when expected. 
    // CSR checks are done in other assertions
    property p_enter_debug;
        $changed(debug_cause_pri) && (debug_cause_pri != 3'b000) && !cov_assert_if.debug_mode_q
        |-> decode_valid [->1:2] ##0 cov_assert_if.debug_mode_q;
    endproperty
    a_enter_debug: assert property(p_enter_debug)
        else
            `uvm_error(info_tag, $sformatf("Debug mode not entered after exepected cause %d", debug_cause_pri));

    // Checck that depc gets the correct value when debug mode is entered.
    property p_debug_mode_pc;
        $rose(first_debug_ins) |-> cov_assert_if.debug_mode_q && (prev_id_pc == halt_addr_at_entry) && (cov_assert_if.depc_q == pc_at_dbg_req);
    endproperty   

    a_debug_mode_pc: assert property(p_debug_mode_pc)
        else
            `uvm_error(info_tag, $sformatf("Debug mode entered with wrong pc. pc==%08x",prev_id_pc));

    // Check that debug with cause haltreq is correct
    property p_debug_mode_ext_req;
        $rose(cov_assert_if.debug_mode_q) && (cov_assert_if.dcsr_q[8:6] == cv32e40p_pkg::DBG_CAUSE_HALTREQ) 
        |-> debug_cause_pri == cv32e40p_pkg::DBG_CAUSE_HALTREQ;
    endproperty
    
    a_debug_mode_ext_req: assert property(p_debug_mode_ext_req)
        else
            `uvm_error(info_tag, $sformatf("Debug cause not correct for haltreq, cause = %d",cov_assert_if.dcsr_q[8:6]));

    // Check that debug with cause ebreak is correct
    property p_cebreak_debug_mode;
        $rose(cov_assert_if.debug_mode_q) && (cov_assert_if.dcsr_q[8:6] == cv32e40p_pkg::DBG_CAUSE_EBREAK)
        |-> debug_cause_pri == cv32e40p_pkg::DBG_CAUSE_EBREAK;
    endproperty

    a_cebreak_debug_mode: assert property(p_cebreak_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode with wrong cause after ebreak, case = %d",cov_assert_if.dcsr_q[8:6]));

    // c.ebreak without dcsr.ebreakm results in exception at mtvec
    // Exclude single stepping as the sequence gets very complicated
    property p_cebreak_exception;
        disable iff(cov_assert_if.debug_req_i | !cov_assert_if.rst_ni)
        $rose(cov_assert_if.is_cebreak) && cov_assert_if.dcsr_q[15] == 1'b0 && !cov_assert_if.debug_mode_q  && cov_assert_if.is_decoding && cov_assert_if.id_valid &&
        !cov_assert_if.debug_req_i && !cov_assert_if.dcsr_q[2]
        |-> (decode_valid) [->1:2] ##0  !cov_assert_if.debug_mode_q && (cov_assert_if.mcause_q[5:0] === cv32e40p_pkg::EXC_CAUSE_BREAKPOINT) 
                                                                && (cov_assert_if.mepc_q == pc_at_ebreak) &&
                                                                   (cov_assert_if.id_stage_pc == cov_assert_if.mtvec);
    endproperty
    
    a_cebreak_exception: assert property(p_cebreak_exception)
        else
            `uvm_error(info_tag,$sformatf("Exception not entered correctly after c.ebreak with dcsr.ebreak=0"));

    // ebreak without dcsr.ebreakm results in exception at mtvec
    // Exclude single stepping as the sequence gets very complicated
    property p_ebreak_exception;
        disable iff(cov_assert_if.debug_req_i | !cov_assert_if.rst_ni)
        $rose(cov_assert_if.is_ebreak) && cov_assert_if.dcsr_q[15] == 1'b0 && !cov_assert_if.debug_mode_q  && cov_assert_if.is_decoding && cov_assert_if.id_valid &&
        !cov_assert_if.debug_req_i && !cov_assert_if.dcsr_q[2] 
        |-> (decode_valid) [->1:2] ##0  !cov_assert_if.debug_mode_q && (cov_assert_if.mcause_q[5:0] === cv32e40p_pkg::EXC_CAUSE_BREAKPOINT) 
                                                                && (cov_assert_if.mepc_q == pc_at_ebreak) &&
                                                                   (cov_assert_if.id_stage_pc == cov_assert_if.mtvec);
    endproperty
    
    // TODO: Fails formal as above
    a_ebreak_exception: assert property(p_ebreak_exception)
        else
            `uvm_error(info_tag,$sformatf("Exception not entered correctly after ebreak with dcsr.ebreak=0"));
    // c.ebreak during debug mode results in relaunch of debug mode

    property p_cebreak_during_debug_mode;
        $rose(cov_assert_if.is_cebreak) ##0 cov_assert_if.debug_mode_q  |-> decode_valid [->2] ##0 cov_assert_if.debug_mode_q  &&
                                                       (cov_assert_if.id_stage_pc == halt_addr_at_entry); // TODO should check no change in dpc and dcsr
    endproperty

    a_cebreak_during_debug_mode: assert property(p_cebreak_during_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not restarted after c.ebreak"));

    // ebreak during debug mode results in relaunch
    property p_ebreak_during_debug_mode;
        $rose(cov_assert_if.is_ebreak) ##0 cov_assert_if.debug_mode_q   |-> decode_valid [->2] ##0 cov_assert_if.debug_mode_q && 
                                                     (cov_assert_if.id_stage_pc == halt_addr_at_entry); // TODO should check no change in dpc and dcsr
    endproperty

    a_ebreak_during_debug_mode: assert property(p_ebreak_during_debug_mode)
        else
            `uvm_error(info_tag,$sformatf("Debug mode not restarted after ebreak"));

    // Trigger match results in debug mode
    property p_trigger_match;
        cov_assert_if.trigger_match_i ##0 cov_assert_if.tdata1[2] ##0 !cov_assert_if.debug_mode_q ##0 cov_assert_if.id_stage_instr_valid_i ##0 cov_assert_if.is_decoding
        |-> decode_valid [->2] ##0 (cov_assert_if.debug_mode_q && (cov_assert_if.dcsr_q[8:6]=== cv32e40p_pkg::DBG_CAUSE_TRIGGER) && 
                                                            (cov_assert_if.depc_q == tdata2_at_entry)) &&
                                                            (cov_assert_if.id_stage_pc == halt_addr_at_entry);
    endproperty   

    a_trigger_match: assert property(p_trigger_match)
        else
            `uvm_error(info_tag, $sformatf("Debug mode not correctly entered after trigger match depc=%08x,  tdata2=%08x", cov_assert_if.depc_q, tdata2_at_entry)); 

    // Address match without trigger enabled should NOT result in debug mode
    property p_trigger_match_disabled;
        $rose(cov_assert_if.addr_match) && !cov_assert_if.debug_mode_q |-> ##[1:6] !cov_assert_if.debug_mode_q;
    endproperty

    a_trigger_match_disabled: assert property(p_trigger_match_disabled)
        else
            `uvm_error(info_tag, "Trigger match with tdata[2]==0 resulted in debug mode");

    // Exception in debug mode results in pc->dm_exception_addr_i
    property p_debug_mode_exception;
        $rose(cov_assert_if.illegal_insn_i) && cov_assert_if.debug_mode_q && cov_assert_if.is_decoding |-> (decode_valid & cov_assert_if.id_valid) [->2] ##0 cov_assert_if.debug_mode_q && (cov_assert_if.id_stage_pc == exception_addr_at_entry);
    endproperty

    a_debug_mode_exception : assert property(p_debug_mode_exception)
        else
            `uvm_error(info_tag, $sformatf("Exception in debug mode not handled incorrectly. dm=%d, pc=%08x", cov_assert_if.debug_mode_q, cov_assert_if.id_stage_pc));

    // ECALL in debug mode results in pc->dm_exception_addr_i
    property p_debug_mode_ecall;
        $rose(cov_assert_if.ecall_insn_i) && cov_assert_if.debug_mode_q  && cov_assert_if.is_decoding && cov_assert_if.id_stage_instr_valid_i
        |-> (decode_valid & cov_assert_if.id_valid) [->1:3] ##0 cov_assert_if.debug_mode_q && (cov_assert_if.id_stage_pc == exception_addr_at_entry);
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
    // wit cause=haltreq
    property p_sleep_debug_req;
        cov_assert_if.in_wfi && cov_assert_if.debug_req_i |=> !cov_assert_if.core_sleep_o |-> decode_valid [->1:2] ##0 cov_assert_if.debug_mode_q &&
        cov_assert_if.dcsr_q[8:6] == cv32e40p_pkg::DBG_CAUSE_HALTREQ;
    endproperty

    a_sleep_debug_req : assert property(p_sleep_debug_req)
        else
            `uvm_error(info_tag, $sformatf("Did not exit sleep(== %d) after debug_req_i. Debug_mode = %d cause = %d", cov_assert_if.core_sleep_o, cov_assert_if.debug_mode_q, cov_assert_if.dcsr_q[8:6]));

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
                decode_valid [->2] ##0 cov_assert_if.debug_mode_q && !cov_assert_if.core_sleep_o;
    endproperty

    a_single_step_wfi : assert property(p_single_step_wfi)
        else
            `uvm_error(info_tag, "Debug mode not entered after single step WFI or core went sleeping");

    // Executing with single step with no irq results in debug mode
    property p_single_step;
        !cov_assert_if.debug_mode_q && cov_assert_if.dcsr_q[2] && !cov_assert_if.dcsr_q[11] && decode_valid |=>  decode_valid [->1] ##0 cov_assert_if.debug_mode_q;
    endproperty

    a_single_step: assert property(p_single_step)
        else
            `uvm_error(info_tag, "Debug mode not entered for single step");

    // dret in M-mode will cause illegal instruction
    // If pending debug req, illegal insn will not assert
    // until resume
    property p_mmode_dret;
        !cov_assert_if.debug_mode_q && cov_assert_if.is_dret && !cov_assert_if.debug_req_i   |-> ##1 cov_assert_if.illegal_insn_q;
    endproperty

    a_mmode_dret : assert property(p_mmode_dret)
        else
            `uvm_error(info_tag, "Executing dret in M-mode did not result in illegal instruction");

    // dret in D-mode will restore pc and exit D-mode
    property p_dmode_dret;
        cov_assert_if.debug_mode_q && cov_assert_if.is_dret |-> decode_valid [->2] ##0  !cov_assert_if.debug_mode_q && (cov_assert_if.id_stage_pc == cov_assert_if.depc_q);
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
    // Counter can be written an arbitrary value, check that
    // it changed only when not being written to
    property p_mcycle_count;
        !cov_assert_if.mcountinhibit_q[0] && !cov_assert_if.core_sleep_o  && !(cov_assert_if.csr_we_int && (cov_assert_if.csr_addr ==12'hB00 || cov_assert_if.csr_addr == 12'hB80)) |=>  $changed(cov_assert_if.mcycle);
    endproperty

    a_mcycle_count : assert property(p_mcycle_count)
        else
            `uvm_error(info_tag, "Mcycle not counting when mcountinhibit[0] is cleared!");

    // Check that minstret works as expected when not sleeping
    // Check only when not written to
    property p_minstret_count;
        !cov_assert_if.mcountinhibit_q[2] && cov_assert_if.inst_ret && !cov_assert_if.core_sleep_o
        && !(cov_assert_if.csr_we_int && (cov_assert_if.csr_addr == 12'hB02 || cov_assert_if.csr_addr == 12'hB82))
        |=> (cov_assert_if.minstret == ($past(cov_assert_if.minstret)+1));
    endproperty

    a_minstret_count : assert property(p_minstret_count)
        else
            `uvm_error(info_tag, "Minstret not counting when mcountinhibit[2] is cleared!");

    // Check debug_req_i and irq on same cycle. 
    // Should result in debug mode with regular pc in depc,
    // not pc from interrupt handler
    // PC is checked in another assertion
    property p_debug_req_and_irq;
        cov_assert_if.debug_req_i && cov_assert_if.pending_enabled_irq  && cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DECODE
        |-> (decode_valid & cov_assert_if.id_valid) [->1:2] ##0 cov_assert_if.debug_mode_q;
    endproperty

    a_debug_req_and_irq : assert property(p_debug_req_and_irq)
        else
            `uvm_error(info_tag, "Debug mode not entered after debug_req_i and irq on same cycle");

    // debug_req at reset should result in debug mode and no instructions
    // executed
    property p_debug_at_reset;
        cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::RESET && cov_assert_if.debug_req_i |->
        decode_valid [->1:2] ##0 cov_assert_if.debug_mode_q && (cov_assert_if.depc_q == boot_addr_at_entry);
 
    endproperty    

    a_debug_at_reset : assert property(p_debug_at_reset)
        else
            `uvm_error(info_tag, "Debug mode not entered correctly at reset!");

    // Check that we cover the case where a debug_req_i
    // comes while flushing due to an illegal insn, causing
    // dpc to be set to the exception handler entry addr
    property p_illegal_insn_debug_req;
        (cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::FLUSH_EX | cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::FLUSH_WB) && cov_assert_if.illegal_insn_q & cov_assert_if.debug_req_i & !cov_assert_if.debug_mode_q|-> decode_valid [->1:2] ##0 cov_assert_if.debug_mode_q &&  cov_assert_if.depc_q == cov_assert_if.mtvec;
    endproperty
    
    a_illegal_insn_debug_req : assert property(p_illegal_insn_debug_req)
        else
            `uvm_error(info_tag, "Debug mode not entered correctly while handling illegal instruction!");
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
      // Enter wfi if we have a valid instruction, not in debug mode and not
      // single stepping
      if (cov_assert_if.is_wfi && !cov_assert_if.debug_mode_q && cov_assert_if.is_decoding && cov_assert_if.id_stage_instr_valid_i & !cov_assert_if.dcsr_q[2]) begin
        cov_assert_if.in_wfi <= 1'b1;

      end else if (cov_assert_if.pending_enabled_irq || cov_assert_if.debug_req_i)
        cov_assert_if.in_wfi <= 1'b0;
       
    end
  end

  // Capture dm_halt_addr_i value
  always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
      if(!cov_assert_if.rst_ni) begin
          halt_addr_at_entry_flag <= 1'b0;
      end else begin
          if(!halt_addr_at_entry_flag) begin
              if(cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_ID | cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_IF) begin
                  halt_addr_at_entry <= {cov_assert_if.dm_halt_addr_i[31:2], 2'b00};
                  tdata2_at_entry <= cov_assert_if.tdata2;
                  halt_addr_at_entry_flag <= 1'b1;
              end
          end

          // Clear flag while not in dmode or we see ebreak in debug
          if((!cov_assert_if.debug_mode_q & halt_addr_at_entry_flag) | (cov_assert_if.debug_mode_q & (cov_assert_if.is_ebreak | cov_assert_if.is_cebreak)))
              halt_addr_at_entry_flag <= 1'b0;

          // Capture boot addr
          if(cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::BOOT_SET)
              boot_addr_at_entry <= {cov_assert_if.boot_addr_i[31:2], 2'b00};
      end
  end
  always@ (posedge cov_assert_if.clk_i)  begin
      if((cov_assert_if.illegal_insn_i | cov_assert_if.ecall_insn_i) & cov_assert_if.pc_set & cov_assert_if.debug_mode_q)
          exception_addr_at_entry = {cov_assert_if.dm_exception_addr_i[31:2], 2'b00};
  end

    assign cov_assert_if.addr_match   = (cov_assert_if.id_stage_pc == cov_assert_if.tdata2);
    assign cov_assert_if.dpc_will_hit = (cov_assert_if.depc_n == cov_assert_if.tdata2);
    assign cov_assert_if.is_wfi = cov_assert_if.id_stage_instr_valid_i & cov_assert_if.id_valid &
                                  ((cov_assert_if.id_stage_instr_rdata_i & WFI_INSTR_MASK) == WFI_INSTR_DATA);
    assign cov_assert_if.pending_enabled_irq = |(cov_assert_if.irq_i & cov_assert_if.mie_q);
    assign cov_assert_if.is_dret             = cov_assert_if.id_valid & cov_assert_if.id_stage_instr_valid_i & cov_assert_if.is_decoding & (cov_assert_if.id_stage_instr_rdata_i == 32'h7B200073);

    // Track which debug cause should be expected
    always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if( !cov_assert_if.rst_ni) begin
            debug_cause_pri <= 3'b000;
        end else begin
            // Debug evaluated in decode state with valid instructions only
            //if(cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DECODE & !cov_assert_if.debug_mode_q) begin
            if(cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DECODE) begin
                if(cov_assert_if.is_decoding & cov_assert_if.id_stage_instr_valid_i) begin
                    if(cov_assert_if.trigger_match_i)
                        debug_cause_pri <= 3'b010;
                    else if((cov_assert_if.dcsr_q[15]) & (cov_assert_if.is_ebreak | cov_assert_if.is_cebreak))
                        debug_cause_pri <= 3'b001;
                    else if(cov_assert_if.debug_req_i) 
                        debug_cause_pri <= 3'b011;
                    else if(cov_assert_if.dcsr_q[2])
                        debug_cause_pri <= 3'b100;
                    else
                        debug_cause_pri <= 3'b000;

                end

            end else if(cov_assert_if.ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_IF) begin
                if(cov_assert_if.debug_req_i) begin
                    debug_cause_pri <= 3'b011;
                end else if(cov_assert_if.dcsr_q[2]) begin
                    debug_cause_pri <= 3'b100;
                end
            end
        end
    end

    // Track PC in id stage to detect first instruction of debug code
    always@ (posedge cov_assert_if.clk_i or negedge cov_assert_if.rst_ni) begin
        if( !cov_assert_if.rst_ni) begin
            prev_id_pc <= 32'h0;
            first_debug_ins_flag <= 1'b0;
            first_debug_ins <= 1'b0;
        end else begin
            prev_id_pc <= cov_assert_if.id_stage_pc;
            first_debug_ins <= 1'b0;
            if(cov_assert_if.debug_mode_q) begin
                if(!first_debug_ins_flag) begin
                    if(cov_assert_if.is_decoding & cov_assert_if.id_stage_instr_valid_i) begin
                        first_debug_ins_flag <= 1'b1;
                        first_debug_ins <= 1'b1;
                    end
                end
            end else begin
                first_debug_ins_flag <= 1'b0;
            end
        end
    end
endmodule : uvmt_cv32e40p_debug_assert
