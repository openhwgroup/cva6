// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_REQ_ITEM_SV__
`define __UVMA_CVXIF_REQ_ITEM_SV__


/**
 * Object rebuilt from the CVXIF monitor
 */
class uvma_cvxif_req_item_c extends uvm_sequence_item;

   rand x_issue_req issue_req;
   rand x_commit commit_req;

   rand logic issue_valid;
   rand logic issue_ready;
   rand logic commit_valid;
   rand logic result_ready;

   `uvm_object_utils(uvma_cvxif_req_item_c)

   /**
    * Default constructor.
   */
   extern function new(string name="uvma_cvxif_req_item");

endclass : uvma_cvxif_req_item_c

function uvma_cvxif_req_item_c::new(string name="uvma_cvxif_req_item");

   super.new(name);

endfunction : new


`endif // __UVMA_CVXIF_REQ_ITEM_SV__
