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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


class uvme_cvxif_covg_c extends uvm_component;

    /*
    * Class members
    */
   uvma_cvxif_req_item_c    req_item ;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_cvxif_req_item_c )  req_item_fifo;


   `uvm_component_utils(uvme_cvxif_covg_c);

   extern function new(string name = "cvxif_covg", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern task run_phase(uvm_phase phase);

   extern task sample_cvxif_req_i(uvma_cvxif_req_item_c req_item);

    /*
     * Covergroups
    */
covergroup mode_cg(string name)
                  with function sample(uvma_cvxif_req_item_c req_item);
   mode_cp: coverpoint (req_item.issue_req.mode)
      {
       bins u_mode  = {2'b00};
       bins s_mode  = {2'b01};
       bins r_mode  = {2'b10};
       bins m_mode  = {2'b11};
      }

endgroup : mode_cg

endclass : uvme_cvxif_covg_c

function uvme_cvxif_covg_c::new(string name = "cvxif_covg", uvm_component parent = null);
   super.new(name, parent);

   mode_cg = new("mode_cg");

endfunction : new

function void uvme_cvxif_covg_c::build_phase(uvm_phase phase);
   super.build_phase(phase);

   req_item_fifo   = new("req_item_fifo" , this);

endfunction : build_phase

task uvme_cvxif_covg_c::run_phase(uvm_phase phase);
   super.run_phase(phase);

   `uvm_info("CVXIFCOVG", "The CVXIF coverage model is running", UVM_LOW);
   forever begin
      req_item_fifo.get(req_item);
      sample_cvxif_req_i(req_item);
   end

endtask : run_phase

task uvme_cvxif_covg_c::sample_cvxif_req_i(uvma_cvxif_req_item_c req_item);

   mode_cg.sample(req_item);

endtask : sample_cvxif_req_i

