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
    input ctrl_state_e  ctrl_fsm_cs,            // Controller FSM states with debug_req

    // Debug signals
    input        debug_req_pending, // From controller
    input        debug_req_q, // From controller
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



  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge clk_i); endclocking
  default disable iff !(rst_ni);

  // ---------------------------------------------------------------------------
  // covergroups
  // ---------------------------------------------------------------------------
  covergroup cg_debug_mode @(posedge debug_req_pending);
          state: coverpoint ctrl_fsm_cs {
                  bins valid_states[] = { [ctrl_fsm_cs.first:ctrl_fsm_cs.last]}; 
          }
          
  endgroup

  cg_debug_mode cg_debug_mode_i;

  initial begin
      cg_debug_mode_i = new();
  end          


endmodule : uvmt_cv32e40p_debug_assert
