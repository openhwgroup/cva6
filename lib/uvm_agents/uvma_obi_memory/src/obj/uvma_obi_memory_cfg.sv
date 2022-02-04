//
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
//


`ifndef __UVMA_OBI_MEMORY_CFG_SV__
`define __UVMA_OBI_MEMORY_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Open Bus Interface agent (uvma_obi_agent_c) components.
 */
class uvma_obi_memory_cfg_c extends uvm_object;

   // Generic options
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;
   rand uvm_sequencer_arb_mode   sqr_arb_mode;
   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;

   bit                           stall_disable;
   bit                           rvalid_singles_stall;

   string                        mon_logger_name = "OBI";

   // Protocol parameters
   rand uvma_obi_memory_version_enum    version;
   rand bit                             ignore_rready;
   rand int unsigned                    auser_width;
   rand int unsigned                    wuser_width;
   rand int unsigned                    ruser_width;
   rand int unsigned                    achk_width;
   rand int unsigned                    rchk_width;
   rand int unsigned                    addr_width ;
   rand int unsigned                    data_width ;
   rand int unsigned                    id_width   ;
   rand bit                             read_enabled;
   rand bit                             write_enabled;

   rand uvma_obi_memory_mode_enum       drv_mode   ;
   rand uvma_obi_memory_drv_idle_enum   drv_idle   ;

   rand bit                                       drv_slv_gnt;
   rand uvma_obi_memory_drv_slv_gnt_mode_enum     drv_slv_gnt_mode;
   rand int unsigned                              drv_slv_gnt_fixed_latency;
   rand int unsigned                              drv_slv_gnt_random_latency_min;
   rand int unsigned                              drv_slv_gnt_random_latency_max;

   rand uvma_obi_memory_drv_slv_rvalid_mode_enum  drv_slv_rvalid_mode;
   rand int unsigned                              drv_slv_rvalid_fixed_latency;
   rand int unsigned                              drv_slv_rvalid_random_latency_min;
   rand int unsigned                              drv_slv_rvalid_random_latency_max;

   rand uvma_obi_memory_drv_slv_err_mode_enum     drv_slv_err_mode;
   rand int unsigned                              drv_slv_err_ok_wgt;
   rand int unsigned                              drv_slv_err_fault_wgt;
   rand bit                                       drv_slv_err_one_shot_mode;
   bit                                            drv_slv_err_one_shot_flag;

   rand uvma_obi_memory_drv_slv_exokay_mode_enum drv_slv_exokay_mode;
   rand int unsigned                             drv_slv_exokay_failure_wgt;
   rand int unsigned                             drv_slv_exokay_success_wgt;

   // Directed error generation memory address range
   // If the valid bit is asserted any address in range will repsond with error = 1
   bit [31:0]                                    directed_slv_err_addr_min;
   bit [31:0]                                    directed_slv_err_addr_max;
   bit                                           directed_slv_err_valid;

   // Directed exokay generation memory address range
   // if the "valid" bit is asserted any address in range will respond
   // with exokay == 0
   bit [31:0]                                    directed_slv_exokay_addr_min;
   bit [31:0]                                    directed_slv_exokay_addr_max;
   bit                                           directed_slv_exokay_valid;


   `uvm_object_utils_begin(uvma_obi_memory_cfg_c)
      `uvm_field_int (                         enabled          , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active        , UVM_DEFAULT)
      `uvm_field_enum(uvm_sequencer_arb_mode , sqr_arb_mode     , UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled, UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled  , UVM_DEFAULT)

      `uvm_field_int (                         stall_disable            , UVM_DEFAULT)
      `uvm_field_int (                         rvalid_singles_stall     , UVM_DEFAULT)

      `uvm_field_enum(uvma_obi_memory_version_enum, version, UVM_DEFAULT)
      `uvm_field_int (                        auser_width  , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        wuser_width  , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        ruser_width  , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        addr_width   , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        achk_width   , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        rchk_width   , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        data_width   , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        id_width     , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        read_enabled , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                        write_enabled, UVM_DEFAULT | UVM_DEC)
      `uvm_field_enum(uvma_obi_memory_mode_enum               , drv_mode                      , UVM_DEFAULT)
      `uvm_field_enum(uvma_obi_memory_drv_idle_enum           , drv_idle                      , UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_gnt                   , UVM_DEFAULT)
      `uvm_field_enum(uvma_obi_memory_drv_slv_gnt_mode_enum   , drv_slv_gnt_mode              , UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_gnt_fixed_latency     , UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_gnt_random_latency_min, UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_gnt_random_latency_max, UVM_DEFAULT)
      `uvm_field_enum(uvma_obi_memory_drv_slv_rvalid_mode_enum, drv_slv_rvalid_mode              , UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_rvalid_fixed_latency     , UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_rvalid_random_latency_min, UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_rvalid_random_latency_max, UVM_DEFAULT)
      `uvm_field_enum(uvma_obi_memory_drv_slv_err_mode_enum,    drv_slv_err_mode              , UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_err_ok_wgt            , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                                          drv_slv_err_fault_wgt         , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                                          drv_slv_err_one_shot_mode     , UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_err_one_shot_flag     , UVM_DEFAULT)
      `uvm_field_enum(uvma_obi_memory_drv_slv_exokay_mode_enum, drv_slv_exokay_mode        , UVM_DEFAULT)
      `uvm_field_int (                                          drv_slv_exokay_failure_wgt , UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (                                          drv_slv_exokay_success_wgt , UVM_DEFAULT | UVM_DEC)

      `uvm_field_int ( directed_slv_err_addr_min      , UVM_DEFAULT)
      `uvm_field_int ( directed_slv_err_addr_max      , UVM_DEFAULT)
      `uvm_field_int ( directed_slv_err_valid         , UVM_DEFAULT)
      `uvm_field_int ( directed_slv_exokay_addr_min   , UVM_DEFAULT)
      `uvm_field_int ( directed_slv_exokay_addr_max   , UVM_DEFAULT)
      `uvm_field_int ( directed_slv_exokay_valid      , UVM_DEFAULT)
   `uvm_object_utils_end

   constraint defaults_cons {
      soft enabled              == 1;
      soft is_active            == UVM_PASSIVE;
      soft sqr_arb_mode         == UVM_SEQ_ARB_FIFO;
      soft cov_model_enabled    == 0;
      soft trn_log_enabled      == 1;

      soft version                        == UVMA_OBI_MEMORY_VERSION_1P1;
      /*soft*/ ignore_rready              == 1;
      soft auser_width                    == uvma_obi_memory_default_auser_width;
      soft wuser_width                    == uvma_obi_memory_default_wuser_width;
      soft ruser_width                    == uvma_obi_memory_default_ruser_width;
      soft addr_width                     == uvma_obi_memory_default_addr_width ;
      soft data_width                     == uvma_obi_memory_default_data_width ;
      soft id_width                       == uvma_obi_memory_default_id_width   ;
      soft achk_width                     == uvma_obi_memory_default_achk_width ;
      soft rchk_width                     == uvma_obi_memory_default_rchk_width ;
      soft write_enabled                  == 1;
      soft read_enabled                   == 1;
      soft drv_mode                       == UVMA_OBI_MEMORY_MODE_MSTR;
      soft drv_idle                       == UVMA_OBI_MEMORY_DRV_IDLE_ZEROS;
      soft drv_slv_gnt                    == 1;
      soft drv_slv_gnt_fixed_latency      == uvma_obi_memory_default_drv_slv_gnt_fixed_latency;
      soft drv_slv_gnt_random_latency_min == uvma_obi_memory_default_drv_slv_gnt_random_latency_min;
      soft drv_slv_gnt_random_latency_max == uvma_obi_memory_default_drv_slv_gnt_random_latency_max;
      soft drv_slv_rvalid_fixed_latency      == uvma_obi_memory_default_drv_slv_rvalid_fixed_latency;
      soft drv_slv_rvalid_random_latency_min == uvma_obi_memory_default_drv_slv_rvalid_random_latency_min;
      soft drv_slv_rvalid_random_latency_max == uvma_obi_memory_default_drv_slv_rvalid_random_latency_max;
      soft drv_slv_err_mode               == UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_OK;
      soft drv_slv_err_one_shot_mode      == 0;
      soft drv_slv_exokay_mode            == UVMA_OBI_MEMORY_DRV_SLV_EXOKAY_MODE_SUCCESS;
   }

   constraint stall_disable_cons {
      // Implement the plusarg +rand_stall_obi_disable
      stall_disable -> (drv_slv_gnt_mode == UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_CONSTANT);
      stall_disable -> (drv_slv_rvalid_mode == UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_CONSTANT);
   }

   constraint rvalid_single_stall_cons {
      // Implement the plusarg +rand_stall_obi_disabl
      // 0-cycle gnt stall
      // 1-cycle rvalid stall
      if (rvalid_singles_stall) {
         drv_slv_gnt_mode == UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_FIXED_LATENCY;
         drv_slv_gnt_fixed_latency == 0;

         drv_slv_rvalid_mode == UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_FIXED_LATENCY;
         drv_slv_rvalid_fixed_latency == 1;
      }
   }

   constraint gnt_min_max_cons {
      drv_slv_gnt_random_latency_min <= drv_slv_gnt_random_latency_max;
   }

   constraint rvalid_min_max_cons {
      drv_slv_rvalid_random_latency_min <= drv_slv_rvalid_random_latency_max;
   }

   constraint err_wgts_cons {
      // Keep the weights for errors within some bounds
      drv_slv_err_ok_wgt    inside {[0:1000]};
      drv_slv_err_fault_wgt inside {[0:1000]};
   }

   constraint exokay_wgts_cons {
      // Keep the weights for exokay response within some bounds
      drv_slv_exokay_success_wgt inside {[0:1000]};
      drv_slv_exokay_failure_wgt inside {[0:1000]};
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_cfg");

   /**
    * Calculate a new random gnt latency
    */
   extern function int unsigned calc_random_gnt_latency();

   /**
    * Calculate a new random rvalid latency
    */
   extern function int unsigned calc_random_rvalid_latency();

   /**
    * Calculate a random bus error from random knobs
    */
   extern function bit calc_random_err(bit[31:0] addr);

   /**
    * Calculate a random atomic exokay response from random knobs
    */
   extern function bit calc_random_exokay(bit[31:0] addr);

   /**
    * Returns 1 if this OBI agent supports version 1.2 or higher
    */
   extern function bit is_1p2_or_higher();

endclass : uvma_obi_memory_cfg_c


function uvma_obi_memory_cfg_c::new(string name="uvma_obi_memory_cfg");

   super.new(name);

   // Read plusargs to determine any special randomizations
   if ($test$plusargs("rand_stall_obi_disable")) begin
      stall_disable = 1;
   end
   else if ($test$plusargs("rvalid_singles_stall")) begin
      rvalid_singles_stall = 1;
   end

endfunction : new


function int unsigned uvma_obi_memory_cfg_c::calc_random_gnt_latency();

   int unsigned effective_latency;

   case (drv_slv_gnt_mode)
      UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_CONSTANT      : effective_latency = 0;
      UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_FIXED_LATENCY : effective_latency = drv_slv_gnt_fixed_latency;
      UVMA_OBI_MEMORY_DRV_SLV_GNT_MODE_RANDOM_LATENCY: begin
         // SVTB.29.1.3.1 - Banned random number system functions and methods calls
         // Waive-abe because drv_slv_gnt_* are constrainable.
         //@DVT_LINTER_WAIVER_START "MT20211214_7" disable SVTB.29.1.3.1
         effective_latency = $urandom_range(drv_slv_gnt_random_latency_min, drv_slv_gnt_random_latency_max);
         //@DVT_LINTER_WAIVER_END "MT20211214_7"
      end
   endcase

   return effective_latency;

endfunction : calc_random_gnt_latency

function int unsigned uvma_obi_memory_cfg_c::calc_random_rvalid_latency();

   int unsigned effective_latency;

   case (drv_slv_rvalid_mode)
      UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_CONSTANT      : effective_latency = 0;
      UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_FIXED_LATENCY : effective_latency = drv_slv_rvalid_fixed_latency;
      UVMA_OBI_MEMORY_DRV_SLV_RVALID_MODE_RANDOM_LATENCY: begin
         //@DVT_LINTER_WAIVER_START "MT20211214_8" disable SVTB.29.1.3.1
         effective_latency = $urandom_range(drv_slv_rvalid_random_latency_min, drv_slv_rvalid_random_latency_max);
         //@DVT_LINTER_WAIVER_END "MT20211214_8"
      end
   endcase

   return effective_latency;

endfunction : calc_random_rvalid_latency

function bit uvma_obi_memory_cfg_c::calc_random_err(bit[31:0] addr);

   bit err;

   // If we are in "one-shot" mode and have already calculated an error,
   // then skip any new errors (until the code resets the flag)
   if (drv_slv_err_one_shot_mode && drv_slv_err_one_shot_flag) begin
      return 0;
   end

   // Check for a directed error reponse first
   if (directed_slv_err_valid &&
       (addr >= directed_slv_err_addr_min) &&
       (addr <= directed_slv_err_addr_max)) begin

      if (drv_slv_err_one_shot_mode) begin
         drv_slv_err_one_shot_flag = 1;
      end

      return 1;
   end

   case (drv_slv_err_mode)
      UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_OK      : err = 0;
      UVMA_OBI_MEMORY_DRV_SLV_ERR_MODE_RANDOM  : begin
         randcase
            drv_slv_err_ok_wgt:    err = 0;
            drv_slv_err_fault_wgt: err = 1;
         endcase
      end
   endcase

   if (err && drv_slv_err_one_shot_mode) begin
      drv_slv_err_one_shot_flag = 1;
   end

   return err;

endfunction : calc_random_err

function bit uvma_obi_memory_cfg_c::calc_random_exokay(bit[31:0] addr);

   bit exokay;

   // Check for a directed error reponse first
   if (directed_slv_exokay_valid &&
       (addr <= directed_slv_exokay_addr_min) &&
       (addr <= directed_slv_exokay_addr_min)) begin
      return 0;
   end

   case (drv_slv_exokay_mode)
      UVMA_OBI_MEMORY_DRV_SLV_EXOKAY_MODE_SUCCESS : exokay = 1;
      UVMA_OBI_MEMORY_DRV_SLV_EXOKAY_MODE_RANDOM  : begin
         randcase
            drv_slv_exokay_success_wgt: exokay = 1;
            drv_slv_exokay_failure_wgt: exokay = 0;
         endcase
      end
   endcase

   return exokay;

endfunction : calc_random_exokay

function bit uvma_obi_memory_cfg_c::is_1p2_or_higher();

   return (version >= UVMA_OBI_MEMORY_VERSION_1P2) ? 1 : 0;

endfunction : is_1p2_or_higher

`endif // __UVMA_OBI_MEMORY_CFG_SV__


