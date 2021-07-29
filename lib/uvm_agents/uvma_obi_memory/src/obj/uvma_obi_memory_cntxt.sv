// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVMA_OBI_MEMORY_CNTXT_SV__
`define __UVMA_OBI_MEMORY_CNTXT_SV__


// Forward type declarations
typedef class uvma_obi_memory_mon_trn_c;


/**
 * Object encapsulating all state variables for all Open Bus Interface agent
 * (uvma_obi_agent_c) components.
 */
class uvma_obi_memory_cntxt_c extends uvm_object;
   
   // Handle to agent interface
   virtual uvma_obi_memory_if  vif;
   
   // Handle to memory storage for active slaves
   uvml_mem_c mem;

   // Integrals
   uvma_obi_memory_reset_state_enum  reset_state        = UVMA_OBI_MEMORY_RESET_STATE_PRE_RESET;
   uvma_obi_memory_phases_enum       mon_phase          = UVMA_OBI_MEMORY_PHASE_INACTIVE;
   int unsigned               mon_gnt_latency    = 0;
   int unsigned               mon_rvalid_latency = 0;
   int unsigned               mon_rready_latency = 0;
   int unsigned               mon_rp_hold        = 0;
   
   // Queues
   uvma_obi_memory_mon_trn_c  mon_outstanding_reads_q[$];
   
   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;
   
   
   `uvm_object_utils_begin(uvma_obi_memory_cntxt_c)
      `uvm_field_enum(uvma_obi_memory_reset_state_enum, reset_state, UVM_DEFAULT)
      `uvm_field_enum(uvma_obi_memory_phases_enum     , mon_phase  , UVM_DEFAULT)
      
      `uvm_field_queue_object(mon_outstanding_reads_q, UVM_DEFAULT)
      
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Builds events.
    */
   extern function new(string name="uvma_obi_memory_cntxt");
   
   /**
    * TODO Describe uvma_obi_memory_cntxt_c::reset()
    */
   extern function void reset();
   
endclass : uvma_obi_memory_cntxt_c


function uvma_obi_memory_cntxt_c::new(string name="uvma_obi_memory_cntxt");
   
   super.new(name);
   
   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");
   
endfunction : new


function void uvma_obi_memory_cntxt_c::reset();
   
   mon_phase          = UVMA_OBI_MEMORY_PHASE_INACTIVE;
   mon_gnt_latency    = 0;
   mon_rvalid_latency = 0;
   mon_rready_latency = 0;
   mon_rp_hold        = 0;
   
   mon_outstanding_reads_q.delete();
   
endfunction : reset


`endif // __UVMA_OBI_MEMORY_CNTXT_SV__
