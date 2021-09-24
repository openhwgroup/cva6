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


`ifndef __UVME_CV32E40P_CFG_SV__
`define __UVME_CV32E40P_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running
 * CV32E40P environment (uvme_cv32e40p_env_c) components.
 */
class uvme_cv32e40p_cfg_c extends uvm_object;

   // Integrals
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand bit                      scoreboarding_enabled;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;
   rand int unsigned             sys_clk_period;
   //rand int unsigned             debug_clk_period;

   // Random knobs
   rand bit                   zero_stall_sim; // When randomized to 1, clears is_stall_sim in step and compare
   bit                        max_data_zero_instr_stall; // state variable set by plusarg +max_data_zero_instr_stall

   // Agent cfg handles
   rand uvma_clknrst_cfg_c    clknrst_cfg;
   rand uvma_interrupt_cfg_c  interrupt_cfg;
   rand uvma_debug_cfg_c      debug_cfg;
   rand uvma_obi_memory_cfg_c obi_memory_instr_cfg;
   rand uvma_obi_memory_cfg_c obi_memory_data_cfg;

   // Objects
   // TODO Add scoreboard configuration handles
   //      Ex: rand uvml_sb_cfg_c  sb_egress_cfg;
   //          rand uvml_sb_cfg_c  sb_ingress_cfg;


   `uvm_object_utils_begin(uvme_cv32e40p_cfg_c)
      `uvm_field_int (                         enabled                   , UVM_DEFAULT          )
      `uvm_field_enum(uvm_active_passive_enum, is_active                 , UVM_DEFAULT          )
      `uvm_field_int (                         scoreboarding_enabled     , UVM_DEFAULT          )
      `uvm_field_int (                         cov_model_enabled         , UVM_DEFAULT          )
      `uvm_field_int (                         trn_log_enabled           , UVM_DEFAULT          )
      `uvm_field_int (                         sys_clk_period            , UVM_DEFAULT + UVM_DEC)
      //`uvm_field_int (                         debug_clk_period            , UVM_DEFAULT + UVM_DEC)

      `uvm_field_object(clknrst_cfg         , UVM_DEFAULT)
      `uvm_field_object(interrupt_cfg       , UVM_DEFAULT)
      `uvm_field_object(debug_cfg           , UVM_DEFAULT)
      `uvm_field_object(obi_memory_instr_cfg, UVM_DEFAULT)
      `uvm_field_object(obi_memory_data_cfg , UVM_DEFAULT)

      // TODO Add scoreboard cfg field macros
      //      Ex: `uvm_field_object(sb_egress_cfg , UVM_DEFAULT)
      //          `uvm_field_object(sb_ingress_cfg, UVM_DEFAULT)
   `uvm_object_utils_end


   constraint defaults_cons {
      soft enabled                == 0;
      soft is_active              == UVM_PASSIVE;
      soft scoreboarding_enabled  == 1;
      soft cov_model_enabled      == 1;
      soft trn_log_enabled        == 1;
      soft sys_clk_period         == uvme_cv32e40p_sys_default_clk_period; // see uvme_cv32e40p_constants.sv
      //soft debug_clk_period       == uvme_cv32e40p_debug_default_clk_period;
   }

   constraint zero_stall_sim_dist_cons {
      zero_stall_sim dist { 0 :/ 2,  1 :/ 1};
   }

   constraint zero_stall_sim_cons {
      if (zero_stall_sim) {
         obi_memory_instr_cfg.drv_slv_gnt_mode    == UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_CONSTANT;
         obi_memory_instr_cfg.drv_slv_rvalid_mode == UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_CONSTANT;
         obi_memory_data_cfg.drv_slv_gnt_mode     == UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_CONSTANT;
         obi_memory_data_cfg.drv_slv_rvalid_mode  == UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_CONSTANT;
      }
   }

   constraint max_data_zero_instr_stall_sim_cons {
      if (max_data_zero_instr_stall) {
         obi_memory_instr_cfg.drv_slv_gnt_mode    == UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_CONSTANT;
         obi_memory_instr_cfg.drv_slv_rvalid_mode == UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_CONSTANT;

         obi_memory_data_cfg.drv_slv_gnt_mode    == UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_RANDOM_LATENCY;
         obi_memory_data_cfg.drv_slv_gnt_random_latency_min == 0;
         obi_memory_data_cfg.drv_slv_gnt_random_latency_max == 8;

         obi_memory_data_cfg.drv_slv_rvalid_mode == UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_RANDOM_LATENCY;
         obi_memory_data_cfg.drv_slv_rvalid_random_latency_min == 0;
         obi_memory_data_cfg.drv_slv_rvalid_random_latency_max == 8;
      }
   }

   constraint agent_cfg_cons {
      if (enabled) {
         clknrst_cfg.enabled           == 1;
         interrupt_cfg.enabled         == 1;
         debug_cfg.enabled             == 1;
         obi_memory_instr_cfg.enabled  == 1;
         obi_memory_data_cfg.enabled   == 1;
      }

      obi_memory_instr_cfg.version       == UVMA_OBI_MEMORY_VERSION_1P1;
      obi_memory_instr_cfg.drv_mode      == UVMA_OBI_MEMORY_MODE_SLV;
      obi_memory_instr_cfg.write_enabled == 0;
      obi_memory_instr_cfg.addr_width    == 32;
      obi_memory_instr_cfg.data_width    == 32;
      obi_memory_instr_cfg.id_width      == 0;
      obi_memory_instr_cfg.achk_width    == 0;
      obi_memory_instr_cfg.rchk_width    == 0;
      obi_memory_instr_cfg.auser_width   == 0;
      obi_memory_instr_cfg.ruser_width   == 0;
      obi_memory_instr_cfg.wuser_width   == 0;
      soft obi_memory_instr_cfg.drv_slv_gnt_random_latency_max    <= 2;
      soft obi_memory_instr_cfg.drv_slv_gnt_fixed_latency         <= 2;
      soft obi_memory_instr_cfg.drv_slv_rvalid_random_latency_max <= 3;
      soft obi_memory_instr_cfg.drv_slv_rvalid_fixed_latency      <= 3;

      obi_memory_data_cfg.version        == UVMA_OBI_MEMORY_VERSION_1P1;
      obi_memory_data_cfg.drv_mode       == UVMA_OBI_MEMORY_MODE_SLV;
      obi_memory_data_cfg.addr_width     == 32;
      obi_memory_data_cfg.data_width     == 32;
      obi_memory_data_cfg.id_width       == 0;
      obi_memory_data_cfg.achk_width     == 0;
      obi_memory_data_cfg.rchk_width     == 0;
      obi_memory_data_cfg.auser_width    == 0;
      obi_memory_data_cfg.ruser_width    == 0;
      obi_memory_data_cfg.wuser_width    == 0;
      soft obi_memory_data_cfg.drv_slv_gnt_random_latency_max    <= 2;
      soft obi_memory_data_cfg.drv_slv_gnt_fixed_latency         <= 2;
      soft obi_memory_data_cfg.drv_slv_rvalid_random_latency_max <= 3;
      soft obi_memory_data_cfg.drv_slv_rvalid_fixed_latency      <= 3;

      if (is_active == UVM_ACTIVE) {
         clknrst_cfg.is_active           == UVM_ACTIVE;
         interrupt_cfg.is_active         == UVM_ACTIVE;
         debug_cfg.is_active             == UVM_ACTIVE;
         obi_memory_instr_cfg.is_active  == UVM_ACTIVE;
         obi_memory_data_cfg.is_active   == UVM_ACTIVE;
      }

      if (trn_log_enabled) {
         clknrst_cfg.trn_log_enabled           == 1;
         interrupt_cfg.trn_log_enabled         == 1;
         debug_cfg.trn_log_enabled             == 1;
         obi_memory_instr_cfg.trn_log_enabled  == 1;
         obi_memory_data_cfg.trn_log_enabled   == 1;
      }

      if (cov_model_enabled) {
         obi_memory_instr_cfg.cov_model_enabled  == 1;
         obi_memory_data_cfg.cov_model_enabled   == 1;
      }

   }

   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvme_cv32e40p_cfg");

   extern function void pre_randomize();

endclass : uvme_cv32e40p_cfg_c


function uvme_cv32e40p_cfg_c::new(string name="uvme_cv32e40p_cfg");

   super.new(name);

   clknrst_cfg           = uvma_clknrst_cfg_c   ::type_id::create("clknrst_cfg"         );
   interrupt_cfg         = uvma_interrupt_cfg_c ::type_id::create("interrupt_cfg"       );
   debug_cfg             = uvma_debug_cfg_c     ::type_id::create("debug_cfg"           );
   obi_memory_instr_cfg  = uvma_obi_memory_cfg_c::type_id::create("obi_memory_instr_cfg");
   obi_memory_data_cfg   = uvma_obi_memory_cfg_c::type_id::create("obi_memory_data_cfg" );

endfunction : new

function void uvme_cv32e40p_cfg_c::pre_randomize();

   if ($test$plusargs("rand_stall_obi_disable")) begin
      int retval;

      zero_stall_sim = 1;
      zero_stall_sim.rand_mode(0);

      // Hack-set is_stall_sim bit in step_compare
      retval = uvm_hdl_deposit("uvmt_cv32e40p_tb.step_compare.is_stall_sim", 0);
      if (!retval) begin
         `uvm_fatal("ZEROSTALL", "Cannot set is_stall_sim in step_compare")
      end
   end
   else if ($test$plusargs("max_data_zero_instr_stall")) begin
      // No stalls on the I bus, max on D bus
      max_data_zero_instr_stall = 1;
   end

endfunction : pre_randomize


`endif // __UVME_CV32E40P_CFG_SV__

