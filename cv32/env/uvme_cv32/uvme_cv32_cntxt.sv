// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVME_CV32_CNTXT_SV__
`define __UVME_CV32_CNTXT_SV__


/**
 * Object encapsulating all state variables for CV32 environment
 * (uvme_cv32_env_c) components.
 */
class uvme_cv32_cntxt_c extends uvm_object;

   // Virtual interface for ISA coverage
   virtual uvmt_cv32_isa_covg_if isa_covg_vif;

   // Agent context handles
   uvma_clknrst_cntxt_c    clknrst_cntxt;
   uvma_interrupt_cntxt_c  interrupt_cntxt;
   uvma_debug_cntxt_c    debug_cntxt;
   
   // TODO Add scoreboard context handles
   //      Ex: uvme_cv32_sb_cntxt_c  sb_egress_cntxt;
   //          uvme_cv32_sb_cntxt_c  sb_ingress_cntxt;
   
   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;
   
   
   `uvm_object_utils_begin(uvme_cv32_cntxt_c)
      `uvm_field_object(clknrst_cntxt, UVM_DEFAULT)
      `uvm_field_object(interrupt_cntxt, UVM_DEFAULT)
      `uvm_field_object(debug_cntxt  , UVM_DEFAULT)
      
      // TODO Add scoreboard context field macros
      //      Ex: `uvm_field_object(sb_egress_cntxt , UVM_DEFAULT)
      //          `uvm_field_object(sb_ingress_cntxt, UVM_DEFAULT)
      
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Builds events and sub-context objects.
    */
   extern function new(string name="uvme_cv32_cntxt");
   
endclass : uvme_cv32_cntxt_c


function uvme_cv32_cntxt_c::new(string name="uvme_cv32_cntxt");
   
   super.new(name);
   
   clknrst_cntxt = uvma_clknrst_cntxt_c::type_id::create("clknrst_cntxt");
   interrupt_cntxt = uvma_interrupt_cntxt_c::type_id::create("interrupt_cntxt");
   debug_cntxt = uvma_debug_cntxt_c::type_id::create("debug_cntxt");
   
   // TODO Create uvme_cv32_cntxt_c scoreboard context objects
   //      Ex: sb_egress_cntxt  = uvma_cv32_sb_cntxt_c::type_id::create("sb_egress_cntxt" );
   //          sb_ingress_cntxt = uvma_cv32_sb_cntxt_c::type_id::create("sb_ingress_cntxt");
   
   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");
   
endfunction : new


`endif // __UVME_CV32_CNTXT_SV__
