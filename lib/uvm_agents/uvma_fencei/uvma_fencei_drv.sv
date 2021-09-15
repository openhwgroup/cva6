//
// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
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


`ifndef __UVMA_FENCEI_DRV_SV__
`define __UVMA_FENCEI_DRV_SV__


/**
 * Component driving a Open Bus Interface virtual interface (uvma_obi_if).
 * @note The req & rsp's roles are switched when this driver is in 'slv' mode.
 * @todo Move implementation to a sequence-based approach
 */
class uvma_fencei_drv_c extends uvm_driver#(
   .REQ(uvma_fencei_seq_item_c),
   .RSP(uvma_fencei_seq_item_c      )
);

   // Objects
   uvma_fencei_cfg_c    cfg;
   uvma_fencei_cntxt_c  cntxt;

   `uvm_component_utils_begin(uvma_fencei_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_fencei_drv", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Oversees driving, depending on the reset state, by calling drv_<pre|in|post>_reset() tasks.
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Called by run_phase() while agent is in pre-reset state.
    */
   extern task drv_pre_reset();

   /**
    * Called by run_phase() while agent is in reset state.
    */
   extern task drv_in_reset();

   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern task drv_post_reset();

   /**
    * Drives the 'flush_ack' signal in response to 'flush_req' being asserted.
    */
   extern task drv_slv_flush_ack();

endclass : uvma_fencei_drv_c


function uvma_fencei_drv_c::new(string name="uvma_fencei_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_fencei_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_fencei_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_fencei_cfg_c)::set(this, "*", "cfg", cfg);

   void'(uvm_config_db#(uvma_fencei_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_fencei_cntxt_c)::set(this, "*", "cntxt", cntxt);

endfunction : build_phase


task uvma_fencei_drv_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   if (cfg.enabled && cfg.is_active) begin
      fork
         begin
            forever begin
               drv_slv_flush_ack();
            end
         end

         begin
            forever begin
               case (cntxt.reset_state)
                  UVMA_FENCEI_RESET_STATE_PRE_RESET : drv_pre_reset ();
                  UVMA_FENCEI_RESET_STATE_IN_RESET  : drv_in_reset  ();
                  UVMA_FENCEI_RESET_STATE_POST_RESET: drv_post_reset();

                  default: `uvm_fatal("FENCEI_DRV", $sformatf("Invalid reset_state: %0d", cntxt.reset_state))
               endcase
            end
         end
      join_none
   end

endtask : run_phase


task uvma_fencei_drv_c::drv_pre_reset();

   cntxt.fencei_vif.drv_slv_cb.flush_ack  <= 1'b0;
   @(cntxt.fencei_vif.drv_slv_cb);

endtask : drv_pre_reset


task uvma_fencei_drv_c::drv_in_reset();

   cntxt.fencei_vif.drv_slv_cb.flush_ack <= 1'b0;
   @(cntxt.fencei_vif.drv_slv_cb);

endtask : drv_in_reset


task uvma_fencei_drv_c::drv_post_reset();

   @(cntxt.fencei_vif.drv_slv_cb);

endtask : drv_post_reset


task uvma_fencei_drv_c::drv_slv_flush_ack();

   case (cntxt.reset_state)
      UVMA_FENCEI_RESET_STATE_POST_RESET: begin

         // Pre-calculate the "next" latency
         int unsigned effective_latency = cfg.calc_random_ack_latency();

         // In case 0 latency was selected, we must go ahead and drive gnt (combinatorial path)
         if (effective_latency == 0) begin
            cntxt.fencei_vif.drv_slv_cb.flush_ack <= 1'b1;
         end
         else begin
            cntxt.fencei_vif.drv_slv_cb.flush_ack <= 1'b0;
         end

         // Advance the clock
         @(cntxt.fencei_vif.drv_slv_cb);

         // Break out of this loop upon the next req and gnt
         while (!(cntxt.fencei_vif.drv_slv_cb.flush_req && cntxt.fencei_vif.drv_slv_cb.flush_ack)) begin
            // Only count down a non-zero effective latency if someone is requesting (req asserted)
            if (effective_latency && cntxt.fencei_vif.drv_slv_cb.flush_req)
               effective_latency--;

            if (!effective_latency) begin
               cntxt.fencei_vif.drv_slv_cb.flush_ack <= 1'b1;
            end

            @(cntxt.fencei_vif.drv_slv_cb);
         end
      end
      // If we are in another reset state, it is critical to advance time within the reset loop
      default: @(cntxt.fencei_vif.drv_slv_cb);
   endcase

endtask : drv_slv_flush_ack


`endif // __UVMA_FENCEI_DRV_SV__
