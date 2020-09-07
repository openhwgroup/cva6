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

    // Debug signals
    input              debug_req_i, // From controller
    input              debug_mode_q, // From controller
    input logic [31:0] dcsr_q, // From controller
    input logic [31:0] depc_q, // From cs regs
    input logic [31:0] dm_halt_addr_i,
    input logic [31:0] dm_exception_addr_i,
    // WFI Interface
    input core_sleep_o
  );

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------  

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "CV32E40P_DEBUG_ASSERT";
 
  logic is_ebreak; // compiler cannot generate uncompressed ebreak yet(?)
  logic is_cebreak;

  logic [31:0] pc_at_dbg_req; // Capture PC when debug_req_i or ebreak is active
    
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
          state: coverpoint ctrl_fsm_cs {
                  bins valid_states[] = { [ctrl_fsm_cs.first:ctrl_fsm_cs.last]}; 
          }
  endgroup

  // Cover that we execute ebreak with dcsr.ebreakm==1
  covergroup cg_ebreak_execute_with_ebreakm @(posedge clk_i);
          ex: coverpoint is_ebreak==1'b1;
          ebreakm_set: coverpoint dcsr_q[15] == 1'b1;
          test: cross ex, ebreakm_set;  
  endgroup
    
  // Cover that we execute c.ebreak with dcsr.ebreakm==1
  covergroup cg_cebreak_execute_with_ebreakm @(posedge clk_i);
          ex: coverpoint is_cebreak==1'b1;
          ebreakm_set: coverpoint dcsr_q[15] == 1'b1;
          test: cross ex, ebreakm_set;  
  endgroup

  // cg instances
  cg_debug_mode_ext cg_debug_mode_i;
  cg_ebreak_execute_with_ebreakm cg_ebreak_execute_with_ebreakm_i;
  cg_cebreak_execute_with_ebreakm cg_cebreak_execute_with_ebreakm_i;

  // create cg's at start of simulation
  initial begin
      cg_debug_mode_i = new();
      cg_ebreak_execute_with_ebreakm_i = new();
      cg_cebreak_execute_with_ebreakm_i = new();
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

    // -------------------------------------------
    // Capture internal states for use in checking
    // -------------------------------------------
    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni) begin
            pc_at_dbg_req <= 32'h0;
        end else begin
            if(ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_ID) begin
                pc_at_dbg_req <= id_stage_pc;
            end else if(ctrl_fsm_cs == cv32e40p_pkg::DBG_TAKEN_IF) begin
                pc_at_dbg_req <= if_stage_pc;
            end

       end

    end        
endmodule : uvmt_cv32e40p_debug_assert
