// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_COV_MODEL_SV__
`define __UVMA_CVXIF_COV_MODEL_SV__


   /*
   * Covergroups
   * Decalred at package-level to enable mutliple instances per monitor class (e.g. read/write)
   */

class uvma_cvxif_cov_model_c extends uvm_component;

   // Objects
   uvma_cvxif_cfg_c         cfg      ;
   uvma_cvxif_cntxt_c       cntxt    ;
   uvma_cvxif_req_item_c    req_item ;
   uvma_cvxif_resp_item_c   resp_item;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_cvxif_req_item_c )  req_item_fifo;
   uvm_tlm_analysis_fifo#(uvma_cvxif_resp_item_c)  resp_item_fifo;

   //covergroup instances
   covergroup result(string name)
                  with function sample(uvma_cvxif_resp_item_c resp_item);

   we_cp: coverpoint (resp_item.result.we)
      {
       bins we_0  = {0};
       bins we_1  = {1};
      }

   exc_cp: coverpoint (resp_item.result.exc)
      {
       bins exc_0  = {0};
       bins exc_1  = {1};
      }

endgroup : result

covergroup issue(string name)
                  with function sample(uvma_cvxif_resp_item_c resp_item);

   writeback_cp: coverpoint (resp_item.issue_resp.writeback)
      {
       bins writeback_0  = {0};
       bins writeback_1  = {1};
      }

   accept_cp: coverpoint (resp_item.issue_resp.accept)
      {
       bins accept_0  = {0};
       bins accept_1  = {1};
      }

   exc_cp: coverpoint (resp_item.issue_resp.exc)
      {
       bins exc_0  = {0};
       bins exc_1  = {1};
      }

endgroup: issue

   `uvm_component_utils_begin(uvma_cvxif_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cvxif_cov_model", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_cfg()
    */
   extern function void sample_cfg();

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_cntxt()
    */
   extern function void sample_cntxt();

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_req_item()
    */
   extern function void sample_req_item(uvma_cvxif_req_item_c req_item);

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_resp_item()
    */
   extern function void sample_resp_item();

endclass : uvma_cvxif_cov_model_c


function uvma_cvxif_cov_model_c::new(string name="uvma_cvxif_cov_model", uvm_component parent=null);

   super.new(name, parent);

   result = new("result");
   issue = new("issue");

endfunction : new


function void uvma_cvxif_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_cvxif_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   req_item_fifo   = new("req_item_fifo" , this);
   resp_item_fifo  = new("resp_item_fifo", this);

endfunction : build_phase


task uvma_cvxif_cov_model_c::run_phase(uvm_phase phase);

   super.run_phase(phase);
   if (cfg.enabled && cfg.cov_model_enabled) begin
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

         // 'mstr' sequence items
         forever begin
            req_item_fifo.get(req_item);
            sample_req_item(req_item);
         end

         // 'slv' sequence items
          forever begin
            resp_item_fifo.get(resp_item);
            sample_resp_item();
         end
      join_none
   end

endtask : run_phase


function void uvma_cvxif_cov_model_c::sample_cfg();

   // TODO Implement uvma_cvxif_cov_model_c::sample_cfg();

endfunction : sample_cfg


function void uvma_cvxif_cov_model_c::sample_cntxt();

   // TODO Implement uvma_cvxif_cov_model_c::sample_cntxt();

endfunction : sample_cntxt


function void uvma_cvxif_cov_model_c::sample_req_item(uvma_cvxif_req_item_c req_item);

  // TODO Implement uvma_cvxif_cov_model_c::sample_req_item();

endfunction : sample_req_item


function void uvma_cvxif_cov_model_c::sample_resp_item();

   // TODO Implement uvma_cvxif_cov_model_c::sample_resp_item();
   result.sample(resp_item);
   issue.sample(resp_item);

endfunction : sample_resp_item


`endif // __UVMA_CVXIF_COV_MODEL_SV__
