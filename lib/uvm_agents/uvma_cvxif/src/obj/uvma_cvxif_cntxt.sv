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

   `uvm_object_utils(uvma_cvxif_cntxt_c)

   /**
    * Builds events.
    */
   extern function new(string name="uvma_cvxif_cntxt");

endclass : uvma_cvxif_cntxt_c


function uvma_cvxif_cntxt_c::new(string name="uvma_cvxif_cntxt");

   super.new(name);

endfunction : new



`endif // __UVMA_CVXIF_CNTXT_SV__
