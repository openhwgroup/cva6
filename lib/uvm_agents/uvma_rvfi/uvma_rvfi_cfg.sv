//
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
//


`ifndef __UVMA_RVFI_CFG_SV__
`define __UVMA_RVFI_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Clock & Reset agent (uvma_rvfi_agent_c) components.
 */
class uvma_rvfi_cfg_c#(int ILEN=DEFAULT_ILEN,
                       int XLEN=DEFAULT_XLEN) extends uvm_object;

   // Core configuration (used to extract list of CSRs)
   uvma_core_cntrl_cfg_c         core_cfg;

   // Common options
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;

   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;

   // Number of instructions that may be retired in a single cycle
   // This number cannot be zero
   rand int unsigned             nret;

   // Configuration of NMI faults
   rand bit                      nmi_load_fault_enabled;
   rand int unsigned             nmi_load_fault_cause;
   rand bit                      nmi_store_fault_enabled;
   rand int unsigned             nmi_store_fault_cause;

   // Enable bus interrupt fault bit
   rand bit                      insn_bus_fault_enabled;
   rand int unsigned             insn_bus_fault_cause;

   // Name for the instruction retirment ports (nret of these)
   string                        instr_name[int];

   `uvm_object_utils_begin(uvma_rvfi_cfg_c)
      `uvm_field_int (                         enabled                    , UVM_DEFAULT)
      `uvm_field_int (                         nret                       , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active                  , UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled          , UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled            , UVM_DEFAULT)
      `uvm_field_int (                         nmi_load_fault_enabled     , UVM_DEFAULT)
      `uvm_field_int (                         nmi_load_fault_cause       , UVM_DEFAULT)
      `uvm_field_int (                         nmi_store_fault_enabled    , UVM_DEFAULT)
      `uvm_field_int (                         nmi_store_fault_cause      , UVM_DEFAULT)
      `uvm_field_int (                         insn_bus_fault_enabled     , UVM_DEFAULT)
      `uvm_field_int (                         insn_bus_fault_cause       , UVM_DEFAULT)
   `uvm_object_utils_end

   constraint valid_nret {
      nret != 0;
   }

   constraint valid_active_passive {
      // Only designed to support passive mode
      is_active == UVM_PASSIVE;
   }

   constraint defaults_cons {
      soft enabled                 == 1;
      soft is_active               == UVM_PASSIVE;
      soft cov_model_enabled       == 0;
      soft trn_log_enabled         == 1;
      soft nret                    == 1;
      soft nmi_load_fault_enabled  == 0;
      soft nmi_load_fault_cause    == 0;
      soft nmi_store_fault_enabled == 0;
      soft nmi_store_fault_cause   == 0;
      soft insn_bus_fault_enabled  == 0;
      soft insn_bus_fault_cause    == 0;
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvfi_cfg");

endclass : uvma_rvfi_cfg_c

function uvma_rvfi_cfg_c::new(string name="uvma_rvfi_cfg");

   super.new(name);

endfunction : new

`endif // __UVMA_RVFI_CFG_SV__


