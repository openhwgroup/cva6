// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
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

`ifndef __UVME_CV32E40P_VP_DEBUG_CONTROL_SEQ_SV__
`define __UVME_CV32E40P_VP_DEBUG_CONTROL_SEQ_SV__

/**
 * Sequence implementing the virtual status flags decoding 
 */
class uvme_cv32e40p_vp_debug_control_seq_c extends uvma_obi_memory_vp_debug_control_seq_c;

   uvme_cv32e40p_cntxt_c cv32e40p_cntxt;

   `uvm_object_utils_begin(uvme_cv32e40p_vp_debug_control_seq_c)
   `uvm_object_utils_end
      
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40p_vp_debug_control_seq_c");
         
   /**
    * Wait for clocks
    */
   extern virtual task wait_n_clocks(int unsigned n);

   /**
    * Asserts the actual interrupt wires
    */
   extern virtual task set_debug_req(bit debug_req);

endclass : uvme_cv32e40p_vp_debug_control_seq_c

function uvme_cv32e40p_vp_debug_control_seq_c::new(string name="uvme_cv32e40p_vp_debug_control_seq_c");
   
   super.new(name);
   
endfunction : new

task uvme_cv32e40p_vp_debug_control_seq_c::wait_n_clocks(int unsigned n);

   repeat (n) @(cv32e40p_cntxt.debug_vif.mon_cb);

endtask : wait_n_clocks

task uvme_cv32e40p_vp_debug_control_seq_c::set_debug_req(bit debug_req);

   cv32e40p_cntxt.debug_vif.drv_cb.debug_drv <= debug_req;

endtask : set_debug_req

`endif // __UVME_CV32E40P_VP_DEBUG_CONTROL_SEQ_SV__
