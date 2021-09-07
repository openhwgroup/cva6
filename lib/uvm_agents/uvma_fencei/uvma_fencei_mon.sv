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


`ifndef __UVMA_FENCEI_MON_SV__
`define __UVMA_FENCEI_MON_SV__


/**
 * Component sampling transactions from a Clock & Reset virtual interface
 * (uvma_fencei_if).
 */
class uvma_fencei_mon_c extends uvm_monitor;

   // Objects
   uvma_fencei_cfg_c    cfg;
   uvma_fencei_cntxt_c  cntxt;

   // TLM
   uvm_analysis_port#(uvma_fencei_seq_item_c)  ap;

   string log_tag = "FENCEIMONLOG";

   `uvm_component_utils_begin(uvma_fencei_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_fencei_mon", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Oversees monitoring via monitor_clk() and monitor_reset() tasks in parallel
    * forks.
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Monitors passive_mp for asynchronous reset and updates the context's reset state.
    */
   extern task observe_reset();

   /**
    * Monitor pre-reset phase
    */
   extern virtual task fencei_mon_pre_reset();

   /**
    * Monitor in-reset phase
    */
   extern virtual task fencei_mon_in_reset();

   /**
    * Monitor post-reset phase
    */
   extern virtual task fencei_mon_post_reset();

endclass : uvma_fencei_mon_c

function uvma_fencei_mon_c::new(string name="uvma_fencei_mon", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvma_fencei_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_fencei_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_fencei_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   ap = new("ap", this);

endfunction : build_phase

task uvma_fencei_mon_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   if (cfg.enabled) begin
      fork
         observe_reset();

         forever begin
            case (cntxt.reset_state)
               UVMA_FENCEI_RESET_STATE_PRE_RESET:  fencei_mon_pre_reset();
               UVMA_FENCEI_RESET_STATE_IN_RESET:   fencei_mon_in_reset();
               UVMA_FENCEI_RESET_STATE_POST_RESET: fencei_mon_post_reset();
            endcase
         end
      join
   end
endtask : run_phase

task uvma_fencei_mon_c::observe_reset();

   forever begin
      wait (cntxt.fencei_vif.reset_n === 0);
      cntxt.reset_state = UVMA_FENCEI_RESET_STATE_IN_RESET;
      `uvm_info("FENCEI_MON", $sformatf("RESET_STATE_IN_RESET"), UVM_NONE)
      wait (cntxt.fencei_vif.reset_n === 1);
      cntxt.reset_state = UVMA_FENCEI_RESET_STATE_POST_RESET;
      `uvm_info("FENCEI_MON", $sformatf("RESET_STATE_POST_RESET"), UVM_NONE)
   end

endtask : observe_reset

task uvma_fencei_mon_c::fencei_mon_pre_reset();

   @(cntxt.fencei_vif.mon_cb);

endtask : fencei_mon_pre_reset

task uvma_fencei_mon_c::fencei_mon_in_reset();

   @(cntxt.fencei_vif.mon_cb);

endtask : fencei_mon_in_reset

task uvma_fencei_mon_c::fencei_mon_post_reset();

   while(1) begin
      @(cntxt.fencei_vif.mon_cb);

      if (cntxt.fencei_vif.mon_cb.flush_req) begin
         uvma_fencei_seq_item_c mon_trn;

         mon_trn = uvma_fencei_seq_item_c::type_id::create("fencei_mon_trn");

         // Wait for acknowledge, incrementing latency
         while (!cntxt.fencei_vif.mon_cb.flush_ack) begin
            mon_trn.ack_latency++;
            @(cntxt.fencei_vif.mon_cb);
         end

         `uvm_info(log_tag, $sformatf("%s", mon_trn.convert2string()), UVM_HIGH);

         ap.write(mon_trn);
      end
   end

endtask : fencei_mon_post_reset

`endif // __UVMA_FENCEI_MON_SV__
