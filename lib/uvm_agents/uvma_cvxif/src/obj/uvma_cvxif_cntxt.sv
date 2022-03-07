// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_CNTXT_SV__
`define __UVMA_CVXIF_CNTXT_SV__


/**
 * Object encapsulating all state variables for all CVXIF agent
 * (uvma_cvxif_agent_c) components.
 */
class uvma_cvxif_cntxt_c extends uvm_object;

   // Handle to agent interface
   virtual uvma_cvxif_intf  vif;

   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;

   `uvm_object_utils_begin(uvma_cvxif_cntxt_c)
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Builds events.
    */
   extern function new(string name="uvma_cvxif_cntxt");

endclass : uvma_cvxif_cntxt_c


function uvma_cvxif_cntxt_c::new(string name="uvma_cvxif_cntxt");

   super.new(name);

   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");

endfunction : new



`endif // __UVMA_CVXIF_CNTXT_SV__
