// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
// Copyright 2021 Thales DIS Design Services SAS
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_CVA6_CFG_SV__
`define __UVME_CVA6_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * CVA6 environment (uvme_cva6_env_c) components.
 */
class uvme_cva6_cfg_c extends uvm_object;

   // Integrals
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;

   rand bit                      scoreboarding_enabled;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;
   rand int unsigned             sys_clk_period;

   // Agent cfg handles
   rand uvma_clknrst_cfg_c    clknrst_cfg;
   rand uvma_cvxif_cfg_c      cvxif_cfg;

   `uvm_object_utils_begin(uvme_cva6_cfg_c)
      `uvm_field_int (                         enabled                     , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active                   , UVM_DEFAULT          )
      `uvm_field_int (                         scoreboarding_enabled       , UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled           , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled             , UVM_DEFAULT          )
      `uvm_field_int (                         sys_clk_period            , UVM_DEFAULT + UVM_DEC)

      `uvm_field_object(clknrst_cfg, UVM_DEFAULT)

      `uvm_field_object(cvxif_cfg, UVM_DEFAULT)

   `uvm_object_utils_end


   constraint defaults_cons {
      soft enabled                == 0;
      soft is_active              == UVM_PASSIVE;
      soft scoreboarding_enabled  == 1;
      soft cov_model_enabled      == 1;
      soft trn_log_enabled        == 1;
      soft sys_clk_period         == uvme_cva6_sys_default_clk_period; // see uvme_cva6_constants.sv
   }

   constraint agent_cfg_cons {
      if (enabled) {
         clknrst_cfg.enabled   == 1;
      }
      if (is_active == UVM_ACTIVE) {
         clknrst_cfg.is_active   == UVM_ACTIVE;
      }

      if (trn_log_enabled) {
         clknrst_cfg.trn_log_enabled   == 1;
      }

      if (cov_model_enabled) {
         cvxif_cfg.cov_model_enabled == 1;
      }

   }

   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvme_cva6_cfg");

endclass : uvme_cva6_cfg_c


function uvme_cva6_cfg_c::new(string name="uvme_cva6_cfg");

   super.new(name);

   clknrst_cfg  = uvma_clknrst_cfg_c::type_id::create("clknrst_cfg");
   cvxif_cfg    = uvma_cvxif_cfg_c::type_id::create("cvxif_cfg");

endfunction : new


`endif // __UVME_CVA6_CFG_SV__
