//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVME_CV32E40S_COV_MODEL_SV__
`define __UVME_CV32E40S_COV_MODEL_SV__


/**
 * Component encapsulating CV32E40S environment's functional coverage model.
 */
class uvme_cv32e40s_cov_model_c extends uvm_component;

   // Objects
   uvme_cv32e40s_cfg_c    cfg;
   uvme_cv32e40s_cntxt_c  cntxt;

   uvme_interrupt_covg    interrupt_covg;
   uvme_debug_covg        debug_covg;
   uvme_exceptions_covg   exceptions_covg;
   uvme_counters_covg     counters_covg;

   `uvm_component_utils_begin(uvme_cv32e40s_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40s_cov_model", uvm_component parent=null);

   /**
    * Ensures cfg & cntxt handles are not null.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Connects ISA coverage model to interrupt coverage model
    */
   extern virtual function void connect_phase(uvm_phase phase);

   /**
    * Describe uvme_cv32e40s_cov_model_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);

endclass : uvme_cv32e40s_cov_model_c


function uvme_cv32e40s_cov_model_c::new(string name="uvme_cv32e40s_cov_model", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvme_cv32e40s_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cv32e40s_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvme_cv32e40s_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   interrupt_covg = uvme_interrupt_covg::type_id::create("interrupt_covg", this);
   uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "interrupt_covg", "cfg", cfg);

   debug_covg = uvme_debug_covg::type_id::create("debug_covg", this);
   uvm_config_db#(uvme_cv32e40s_cntxt_c)::set(this, "debug_covg", "cntxt", cntxt);

   exceptions_covg = uvme_exceptions_covg::type_id::create("exceptions_covg", this);

   counters_covg = uvme_counters_covg::type_id::create("counters_covg", this);
   uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "counters_covg", "cfg", cfg);

endfunction : build_phase

function void uvme_cv32e40s_cov_model_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

endfunction : connect_phase

task uvme_cv32e40s_cov_model_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

endtask : run_phase


`endif // __UVME_CV32E40S_COV_MODEL_SV__
