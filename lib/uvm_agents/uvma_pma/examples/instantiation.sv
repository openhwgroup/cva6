// Copyright 2021 OpenHW Group
// 
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


/**
 * This file contains sample code that demonstrates how to add an instance of the Memory attribution agent for OpenHW Group CORE-V verification testbenches UVM Agent
 * to a UVM environment.
 * NOTE It is recommended to split up class member declaration and definition.  These classes are all inline to keep the
 * example short.
 */


/**
 * Object encapsulating all configuration information for my_env.
 */
class my_env_cfg_c extends uvm_object;
   
   rand uvma_pma_cfg_c  pma_cfg;
   
   `uvm_object_utils_begin(my_env_cfg_c)
      `uvm_field_object(pma_cfg, UVM_DEFAULT)
   `uvm_object_utils_end
   
   constraint defaults_cons {
      soft pma_cfg.enabled == 1;
   }
   
   function new(uvm_component parent=null, string name="my_env");
      super.new(parent, name);
      cfg = uvma_pma_cfg_c::type_id::create("pma_cfg");
   endfunction : new
   
endclass : my_env_cfg_c


/**
 * Component encapsulating the environment.
 */
class my_env_c extends uvm_env;
   
   rand my_env_cfg_c  cfg;
   uvma_pma_agent_c  pma_agent;
   
   `uvm_component_utils_begin(my_env_c)
      `uvm_field_object(cfg, UVM_DEFAULT)
   `uvm_component_utils_end
   
   function new(uvm_component parent=null, string name="my_env");
      super.new(parent, name);
   endfunction : new
   
   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if (!cfg) begin
         `uvm_fatal("MY_ENV", "cfg is null")
      end
      else begin
         uvm_config_db#(uvma_pma_cfg_c)::set(this, "pma_agent", "cfg", cfg.pma_cfg);
         pma_agent = uvma_pma_agent_c::type_id::create("pma_agent", this);
      end
   endfunction : build_phase
   
endclass : my_env_c
