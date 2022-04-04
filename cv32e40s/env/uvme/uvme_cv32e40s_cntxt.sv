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


`ifndef __UVME_CV32E40S_CNTXT_SV__
`define __UVME_CV32E40S_CNTXT_SV__


/**
 * Object encapsulating all state variables for CV32E40S environment
 * (uvme_cv32e40s_env_c) components.
 */
class uvme_cv32e40s_cntxt_c extends uvm_object;

   // Virtual interface for Debug coverage
   virtual uvmt_cv32e40s_debug_cov_assert_if debug_cov_vif;
   virtual uvmt_cv32e40s_vp_status_if        vp_status_vif; ///< Virtual interface for Virtual Peripherals
   virtual uvma_interrupt_if                 intr_vif     ; ///< Virtual interface for interrupts
   virtual uvma_debug_if                     debug_vif    ; ///< Virtual interface for debug

   // Agent context handles
   uvma_cv32e40s_core_cntrl_cntxt_c  core_cntrl_cntxt;
   uvma_clknrst_cntxt_c              clknrst_cntxt;
   uvma_interrupt_cntxt_c            interrupt_cntxt;
   uvma_debug_cntxt_c                debug_cntxt;
   uvma_obi_memory_cntxt_c           obi_memory_instr_cntxt;
   uvma_obi_memory_cntxt_c           obi_memory_data_cntxt;
   uvma_rvfi_cntxt_c#(ILEN,XLEN)     rvfi_cntxt;
   uvma_rvvi_cntxt_c#(ILEN,XLEN)     rvvi_cntxt;
   uvma_fencei_cntxt_c               fencei_cntxt;

   // Memory modelling
   rand uvml_mem_c                   mem;

   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;

   `uvm_object_utils_begin(uvme_cv32e40s_cntxt_c)
      `uvm_field_object(core_cntrl_cntxt,       UVM_DEFAULT)
      `uvm_field_object(clknrst_cntxt,          UVM_DEFAULT)
      `uvm_field_object(interrupt_cntxt,        UVM_DEFAULT)
      `uvm_field_object(debug_cntxt  ,          UVM_DEFAULT)
      `uvm_field_object(obi_memory_instr_cntxt, UVM_DEFAULT)
      `uvm_field_object(obi_memory_data_cntxt , UVM_DEFAULT)
      `uvm_field_object(rvfi_cntxt,             UVM_DEFAULT)
      `uvm_field_object(rvvi_cntxt,             UVM_DEFAULT)
      `uvm_field_object(mem,                    UVM_DEFAULT)

      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end

   constraint mem_cfg_cons {
      mem.mem_default == MEM_DEFAULT_0;
   }

   /**
    * Builds events and sub-context objects.
    */
   extern function new(string name="uvme_cv32e40s_cntxt");

endclass : uvme_cv32e40s_cntxt_c


function uvme_cv32e40s_cntxt_c::new(string name="uvme_cv32e40s_cntxt");

   super.new(name);

   clknrst_cntxt    = uvma_clknrst_cntxt_c::type_id::create("clknrst_cntxt");
   core_cntrl_cntxt = uvma_cv32e40s_core_cntrl_cntxt_c::type_id::create("core_cntrl_cntxt");
   debug_cntxt      = uvma_debug_cntxt_c::type_id::create("debug_cntxt");
   fencei_cntxt     = uvma_fencei_cntxt_c::type_id::create("fencei_cntxt");
   interrupt_cntxt  = uvma_interrupt_cntxt_c::type_id::create("interrupt_cntxt");
   obi_memory_data_cntxt  = uvma_obi_memory_cntxt_c::type_id::create("obi_memory_data_cntxt" );
   obi_memory_instr_cntxt = uvma_obi_memory_cntxt_c::type_id::create("obi_memory_instr_cntxt");
   rvfi_cntxt       = uvma_rvfi_cntxt_c#(ILEN,XLEN)::type_id::create("rvfi_cntxt");
   rvvi_cntxt       = uvma_rvvi_ovpsim_cntxt_c#(ILEN,XLEN)::type_id::create("rvvi_cntxt");

   mem = uvml_mem_c#(XLEN)::type_id::create("mem");

   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");

endfunction : new


`endif // __UVME_CV32E40S_CNTXT_SV__

