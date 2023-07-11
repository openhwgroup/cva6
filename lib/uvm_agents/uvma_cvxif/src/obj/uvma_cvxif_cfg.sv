// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_CFG_SV__
`define __UVMA_CVXIF_CFG_SV__

/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Clock & Reset agent (uvma_cvxif_agent_c) components.
 */
class uvma_cvxif_cfg_c extends uvm_object;

   rand int unsigned uvma_cvxif_issue_ready;
   rand int unsigned uvma_cvxif_issue_not_ready;
   rand uvma_cvxif_ready_mode_enum ready_mode;
   rand logic instr_delayed;
   rand int rnd_delay;
   rand bit in_order;
   rand bit   cov_model_enabled;
   rand bit   enabled;

   rand bit dual_read_write_support_x;
   rand bit load_store_support_x;
   rand bit seq_cus_instr_x2_enabled;
   rand bit reg_cus_crosses_enabled;

   constraint reasonable_values {
      soft uvma_cvxif_issue_ready inside     {[4:10]};
      soft uvma_cvxif_issue_not_ready inside {[1:2]};
      soft rnd_delay inside {[2:4]};
   }

   constraint issue_ready {
      if (uvma_cvxif_issue_ready == 0   || uvma_cvxif_issue_not_ready==0)
          uvma_cvxif_issue_not_ready!=0 ||  uvma_cvxif_issue_ready != 0;
   }

   constraint defaults_val {
      soft ready_mode        == UVMA_CVXIF_ISSUE_READY_FIX; // issue_ready is not randomized => the agent is always ready by default,
                                                            // you can randomize it by giving "UVMA_CVXIF_ISSUE_READY_RANDOMIZED" to "ready_mode"
      soft instr_delayed     == 0;
      soft in_order          == 0;
      soft cov_model_enabled == 0;
      soft enabled           == 1;
   }

   `uvm_object_utils_begin(uvma_cvxif_cfg_c)
      `uvm_field_int ( ready_mode,                     UVM_DEFAULT)
      `uvm_field_int ( uvma_cvxif_issue_ready,         UVM_DEFAULT)
      `uvm_field_int ( uvma_cvxif_issue_not_ready,     UVM_DEFAULT)
      `uvm_field_int ( instr_delayed,                  UVM_DEFAULT)
      `uvm_field_int ( rnd_delay,                      UVM_DEFAULT)
      `uvm_field_int ( in_order,                       UVM_DEFAULT)
      `uvm_field_int ( cov_model_enabled,              UVM_DEFAULT)
      `uvm_field_int ( enabled,                        UVM_DEFAULT)
      `uvm_field_int ( dual_read_write_support_x,      UVM_DEFAULT)
      `uvm_field_int ( load_store_support_x,           UVM_DEFAULT)
      `uvm_field_int ( seq_cus_instr_x2_enabled,       UVM_DEFAULT)
      `uvm_field_int ( reg_cus_crosses_enabled,        UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cvxif_cfg");

endclass : uvma_cvxif_cfg_c


function uvma_cvxif_cfg_c::new(string name="uvma_cvxif_cfg");

   super.new(name);

endfunction : new


`endif //__UVMA_CVXIF_CFG_SV__
