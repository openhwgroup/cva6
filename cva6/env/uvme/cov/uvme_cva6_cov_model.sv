//
// Copyright 2020 OpenHW Group
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


`ifndef __UVME_CVA6_COV_MODEL_SV__
`define __UVME_CVA6_COV_MODEL_SV__


/**
 * Component encapsulating CVA6 environment's functional coverage model.
 */
class uvme_cva6_cov_model_c extends uvm_component;

   // Objects
   uvme_cva6_cfg_c    cfg;
   uvme_cva6_cntxt_c  cntxt;

   // Components
   uvme_cvxif_covg_c  cvxif_covg;

   `uvm_component_utils_begin(uvme_cva6_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cva6_cov_model", uvm_component parent=null);

   /**
    * Ensures cfg & cntxt handles are not null.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Describe uvme_cva6_cov_model_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * TODO Describe uvme_cva6_cov_model_c::sample_cfg()
    */
   extern virtual function void sample_cfg();

   /**
    * TODO Describe uvme_cva6_cov_model_c::sample_cntxt()
    */
   extern virtual function void sample_cntxt();

   // TODO Add coverage functions to uvme_cva6_cov_model_c

endclass : uvme_cva6_cov_model_c


function uvme_cva6_cov_model_c::new(string name="uvme_cva6_cov_model", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvme_cva6_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvme_cva6_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   cvxif_covg = uvme_cvxif_covg_c::type_id::create("cvxif_covg", this);
   uvm_config_db#(uvme_cva6_cfg_c)::set(this, "cvxif_covg", "cfg", cfg);
   uvm_config_db#(uvme_cva6_cntxt_c)::set(this, "cvxif_covg", "cntxt", cntxt);

endfunction : build_phase


task uvme_cva6_cov_model_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   fork
      // Configuration
      forever begin
         cntxt.sample_cfg_e.wait_trigger();
         sample_cfg();
      end

      // Context
      forever begin
         cntxt.sample_cntxt_e.wait_trigger();
         sample_cntxt();
      end

      // TODO Implement uvme_cva6_cov_model_c::run_phase()
      //      Ex: forever begin
      //             debug_fifo.get(debug_trn);
      //             sample_debug();
      //          end
   join_none

endtask : run_phase


function void uvme_cva6_cov_model_c::sample_cfg();

   // TODO Implement uvme_cva6_cov_model_c::sample_cfg();
   //      Ex: cva6_cfg_cg.sample();

endfunction : sample_cfg


function void uvme_cva6_cov_model_c::sample_cntxt();

   // TODO Implement uvme_cva6_cov_model_c::sample_cntxt();
   //      Ex: cva6_cntxt_cg.sample();

endfunction : sample_cntxt


`endif // __UVME_CVA6_COV_MODEL_SV__
