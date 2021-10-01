// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// Copyright 2021 Silicon Labs
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef __UVMA_OBI_MSTR_A_DRV_SV__
`define __UVMA_OBI_MSTR_A_DRV_SV__


/**
 * Component driving a Open Bus Interface virtual interface (uvma_obi_if).
 */
class uvma_obi_drv_mstr_a_c extends uvm_driver #(
   .REQ(uvma_obi_mstr_a_seq_item_c),
   .RSP(uvma_obi_mstr_a_seq_item_c)
);
   
   virtual uvma_obi_if.drv_mstr_a_mp  mp; ///< Handle to virtual interface modport
   
   // Objects
   uvma_obi_cfg_c    cfg  ; ///< Agent configuration handle
   uvma_obi_cntxt_c  cntxt; ///< Agent context handle
   
   // TLM
   uvm_analysis_port#(uvma_obi_mstr_a_seq_item_c)  ap; ///< 
   
   
   `uvm_component_utils_begin(uvma_obi_drv_mstr_a_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_drv_mstr_a", uvm_component parent=null);
   
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
    * Appends cfg, prints out trn and issues heartbeat.
    */
   extern virtual function void process_req(ref uvma_obi_mstr_a_seq_item_c req);
   
   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern virtual task drv_req(ref uvma_obi_mstr_a_seq_item_c req);
   
endclass : uvma_obi_drv_mstr_a_c


function uvma_obi_drv_mstr_a_c::new(string name="uvma_obi_drv_mstr_a", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_drv_mstr_a_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("OBI_MSTR_A_DRV", "Configuration handle is null")
   end
   uvm_config_db#(uvma_obi_cfg_c)::set(this, "*", "cfg", cfg);
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("OBI_MSTR_A_DRV", "Context handle is null")
   end
   uvm_config_db#(uvma_obi_cntxt_c)::set(this, "*", "cntxt", cntxt);
   
   ap = new("ap", this);
   mp = cntxt.vif.drv_mstr_a_mp;
   
endfunction : build_phase


task uvma_obi_drv_mstr_a_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   if (cfg.enabled && cfg.is_active && (cfg.mode == UVMA_OBI_MODE_MSTR)) begin
      forever begin
         seq_item_port.get_next_item(req);
         process_req                (req);
         drv_req                    (req);
         ap.write                   (req);
         
         seq_item_port.item_done();
      end
   end
   
endtask : run_phase


function void uvma_obi_drv_mstr_a_c::process_req(ref uvma_obi_mstr_a_seq_item_c req);
   
   req.cfg = cfg;
   `uvm_info("OBI_MSTR_A_DRV", $sformatf("Got new req from the sequencer:\n%s", req.sprint()), UVM_HIGH)
   
endfunction : process_req


task uvma_obi_drv_mstr_a_c::drv_req(ref uvma_obi_mstr_a_seq_item_c req);
   
   @(mp.drv_mstr_a_cb);
   
   mp.drv_mstr_a_cb.req     <= req.req    ;
   mp.drv_mstr_a_cb.we      <= req.we     ;
   mp.drv_mstr_a_cb.atop    <= req.atop   ;
   mp.drv_mstr_a_cb.memtype <= req.memtype;
   mp.drv_mstr_a_cb.prot    <= req.prot   ;
   mp.drv_mstr_a_cb.reqpar  <= req.reqpar ;
   
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      mp.drv_mstr_a_cb.addr[ii] <= req.addr[ii];
   end
   for (int unsigned ii=0; ii<(cfg.data_width/8); ii++) begin
      mp.drv_mstr_a_cb.be[ii] <= req.be[ii];
   end
   for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
      mp.drv_mstr_a_cb.wdata[ii] <= req.wdata[ii];
   end
   for (int unsigned ii=0; ii<cfg.auser_width; ii++) begin
      mp.drv_mstr_a_cb.auser[ii] <= req.auser[ii];
   end
   for (int unsigned ii=0; ii<cfg.wuser_width; ii++) begin
      mp.drv_mstr_a_cb.wuser[ii] <= req.wuser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      mp.drv_mstr_a_cb.aid[ii] <= req.aid[ii];
   end
   for (int unsigned ii=0; ii<cfg.achk_width; ii++) begin
      mp.drv_mstr_a_cb.achk[ii] <= req.achk[ii];
   end
   
endtask : drv_req


`endif // __UVMA_OBI_MSTR_A_DRV_SV__
