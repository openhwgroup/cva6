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


`ifndef __UVMA_FENCEI_CFG_SV__
`define __UVMA_FENCEI_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Clock & Reset agent (uvma_fencei_agent_c) components.
 */
class uvma_fencei_cfg_c extends uvm_object;

   // Common options
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;

   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;

   // ACK latency modes
   rand uvma_fencei_drv_ack_enum drv_ack_mode;
   rand int unsigned             drv_ack_fixed_latency;
   rand int unsigned             drv_ack_random_latency_min;
   rand int unsigned             drv_ack_random_latency_max;

   `uvm_object_utils_begin(uvma_fencei_cfg_c)
      `uvm_field_int (                          enabled                    , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum,  is_active                  , UVM_DEFAULT)
      `uvm_field_int (                          cov_model_enabled          , UVM_DEFAULT)
      `uvm_field_int (                          trn_log_enabled            , UVM_DEFAULT)
      `uvm_field_enum(uvma_fencei_drv_ack_enum, drv_ack_mode               , UVM_DEFAULT)
      `uvm_field_int (                          drv_ack_fixed_latency      , UVM_DEFAULT)
      `uvm_field_int (                          drv_ack_random_latency_min , UVM_DEFAULT)
      `uvm_field_int (                          drv_ack_random_latency_max , UVM_DEFAULT)
   `uvm_object_utils_end

   constraint defaults_cons {
      soft enabled           == 1;
      soft is_active         == UVM_PASSIVE;
      soft cov_model_enabled == 0;
      soft trn_log_enabled   == 1;
   }

   constraint default_fixed_ack_latency_cons {
      soft drv_ack_fixed_latency inside {[0:12]};
   }

   constraint valid_random_ack_latency_cons {
      drv_ack_random_latency_min <= drv_ack_random_latency_max;
   }

   constraint default_random_latency_cons {
      soft drv_ack_random_latency_min inside {[0:12]};
      soft drv_ack_random_latency_max inside {[0:12]};
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_fencei_cfg");

   /**
    * Calculate a new random gnt latency
    */
   extern function int unsigned calc_random_ack_latency();

endclass : uvma_fencei_cfg_c

function uvma_fencei_cfg_c::new(string name="uvma_fencei_cfg");

   super.new(name);

endfunction : new

function int unsigned uvma_fencei_cfg_c::calc_random_ack_latency();

   int unsigned ack_latency;

   case (drv_ack_mode)
      UVMA_FENCEI_DRV_ACK_MODE_CONSTANT      : ack_latency = 0;
      UVMA_FENCEI_DRV_ACK_MODE_FIXED_LATENCY : ack_latency = drv_ack_fixed_latency;
      UVMA_FENCEI_DRV_ACK_MODE_RANDOM_LATENCY: begin
         ack_latency = $urandom_range(drv_ack_random_latency_min, drv_ack_random_latency_max);
      end
   endcase

   return ack_latency;

endfunction : calc_random_ack_latency

`endif // __UVMA_FENCEI_CFG_SV__

