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


`ifndef __UVMA_OBI_SLV_R_DRV_SV__
`define __UVMA_OBI_SLV_R_DRV_SV__


/**
 * Component driving a Open Bus Interface virtual interface (uvma_obi_if).
 */
class uvma_obi_drv_slv_r_c extends uvm_driver #(
   .REQ(uvma_obi_slv_r_seq_item_c),
   .RSP(uvma_obi_slv_r_seq_item_c)
);
   
   virtual uvma_obi_if.drv_slv_r_mp  mp; ///< Handle to virtual interface modport
   
   // Objects
   uvma_obi_cfg_c    cfg  ; ///< Agent configuration handle
   uvma_obi_cntxt_c  cntxt; ///< Agent context handle
   
   // TLM
   uvm_analysis_port#(uvma_obi_slv_r_seq_item_c)  ap; ///< 
   
   
   `uvm_component_utils_begin(uvma_obi_drv_slv_r_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_drv_slv_r", uvm_component parent=null);
   
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
   extern virtual function void process_req(ref uvma_obi_slv_r_seq_item_c req);
   
   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern virtual task drv_req(ref uvma_obi_slv_r_seq_item_c req);
   
endclass : uvma_obi_drv_slv_r_c


function uvma_obi_drv_slv_r_c::new(string name="uvma_obi_drv_slv_r", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_drv_slv_r_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("OBI_SLV_R_DRV", "Configuration handle is null")
   end
   uvm_config_db#(uvma_obi_cfg_c)::set(this, "*", "cfg", cfg);
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("OBI_SLV_R_DRV", "Context handle is null")
   end
   uvm_config_db#(uvma_obi_cntxt_c)::set(this, "*", "cntxt", cntxt);
   
   ap = new("ap", this);
   mp = cntxt.vif.drv_slv_r_mp;
   
endfunction : build_phase


task uvma_obi_drv_slv_r_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   if (cfg.enabled && cfg.is_active && (cfg.mode == UVMA_OBI_MODE_SLV)) begin
      forever begin
         seq_item_port.get_next_item(req);
         process_req                (req);
         drv_req                    (req);
         ap.write                   (req);
         
         seq_item_port.item_done();
      end
   end
   
endtask : run_phase


function void uvma_obi_drv_slv_r_c::process_req(ref uvma_obi_slv_r_seq_item_c req);
   
   req.cfg = cfg;
   `uvm_info("OBI_SLV_R_DRV", $sformatf("Got new req from the sequencer:\n%s", req.sprint()), UVM_HIGH)
   
endfunction : process_req


task uvma_obi_drv_slv_r_c::drv_req(ref uvma_obi_slv_r_seq_item_c req);
   
   @(mp.drv_mstr_a_cb);
   
   mp.drv_mstr_a_cb.rvalid    <= req.rvalid   ;
   mp.drv_mstr_a_cb.rvalidpar <= req.rvalidpar;
   mp.drv_mstr_a_cb.err       <= req.err      ;
   mp.drv_mstr_a_cb.exokay    <= req.exokay   ;
   
   for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
      mp.drv_mstr_a_cb.rdata[ii] <= req.rdata[ii];
   end
   for (int unsigned ii=0; ii<cfg.ruser_width; ii++) begin
      mp.drv_mstr_a_cb.ruser[ii] <= req.ruser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      mp.drv_mstr_a_cb.rid[ii] <= req.rid[ii];
   end
   for (int unsigned ii=0; ii<cfg.rchk_width; ii++) begin
      mp.drv_mstr_a_cb.rchk[ii] <= req.rchk[ii];
   end
   
endtask : drv_req


`endif // __UVMA_OBI_SLV_R_DRV_SV__
