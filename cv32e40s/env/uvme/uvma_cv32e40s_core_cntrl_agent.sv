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


`ifndef __UVMA_CV32E40S_CORE_CNTRL_AGENT_SV__
`define __UVMA_CV32E40S_CORE_CNTRL_AGENT_SV__

/**
 * Core control agent defined for the CV32E40S
 */
class uvma_cv32e40s_core_cntrl_agent_c extends uvma_core_cntrl_agent_c;


   string log_tag = "CV32E40SCORECTRLAGT";

   `uvm_component_utils_begin(uvma_cv32e40s_core_cntrl_agent_c)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cv32e40s_core_cntrl_agent", uvm_component parent=null);

   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern virtual function void get_and_set_cntxt();

   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this
    * agent.
    */
   extern virtual function void retrieve_vif();

   /**
    * Spawn active sequnces
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Spawn fetch enable control sequence
    */
   extern virtual task start_fetch_toggle_seq();

endclass : uvma_cv32e40s_core_cntrl_agent_c

function uvma_cv32e40s_core_cntrl_agent_c::new(string name="uvma_cv32e40s_core_cntrl_agent", uvm_component parent=null);

   super.new(name, parent);

   set_inst_override_by_type("driver", uvma_core_cntrl_drv_c::get_type(), uvma_cv32e40s_core_cntrl_drv_c::get_type());

endfunction : new

function void uvma_cv32e40s_core_cntrl_agent_c::retrieve_vif();

   uvma_cv32e40s_core_cntrl_cntxt_c e40s_cntxt;

   $cast(e40s_cntxt, cntxt);

   // Core control interface
   if (!uvm_config_db#(virtual uvme_cv32e40s_core_cntrl_if)::get(this, "", $sformatf("core_cntrl_vif"), e40s_cntxt.core_cntrl_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db",
                                    $typename(e40s_cntxt.core_cntrl_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db",
                                 $typename(e40s_cntxt.core_cntrl_vif)), UVM_DEBUG)
   end
endfunction : retrieve_vif

function void uvma_cv32e40s_core_cntrl_agent_c::get_and_set_cntxt();

   void'(uvm_config_db#(uvma_core_cntrl_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_info(log_tag, "Context handle is null; creating", UVM_LOW);
      cntxt = uvma_cv32e40s_core_cntrl_cntxt_c::type_id::create("cntxt");
   end

   uvm_config_db#(uvma_core_cntrl_cntxt_c)::set(this, "*", "cntxt", cntxt);

endfunction : get_and_set_cntxt

task uvma_cv32e40s_core_cntrl_agent_c::run_phase(uvm_phase phase);

   if (cfg.is_active) begin
      fork
         start_fetch_toggle_seq();
      join_none
   end

endtask : run_phase

task uvma_cv32e40s_core_cntrl_agent_c::start_fetch_toggle_seq();

  uvme_cv32e40s_fetch_toggle_seq_c fetch_toggle_seq = uvme_cv32e40s_fetch_toggle_seq_c::type_id::create("fetch_toggle_seq");
  void'(fetch_toggle_seq.randomize());
  fetch_toggle_seq.start(this.sequencer);

endtask : start_fetch_toggle_seq

`endif // __UVMA_CV32E40S_CORE_CNTRL_AGENT_SV__
