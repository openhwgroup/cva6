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


`ifndef __UVMA_OBI_MON_SV__
`define __UVMA_OBI_MON_SV__


/**
 * Component sampling transactions from a Open Bus Interface virtual interface
 * (uvma_obi_if).
 */
class uvma_obi_mon_c extends uvm_monitor;
   
   // Objects
   uvma_obi_cfg_c    cfg;
   uvma_obi_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_obi_mon_trn_c)  ap;
   uvm_analysis_port#(uvma_obi_mon_trn_c)  sequencer_ap;
   
   // Handles to virtual interface modport
   virtual uvma_obi_if.passive_mp  vif_passive_mp;
   
   
   `uvm_component_utils_begin(uvma_obi_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mon", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_mon_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Updates the context's reset state.
    */
   extern task observe_reset();
   
   /**
    * TODO Describe uvma_obi_mon_c::mon_pre_reset()
    */
   extern task mon_pre_reset(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_mon_c::mon_in_reset()
    */
   extern task mon_in_reset(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_mon_c::mon_post_reset()
    */
   extern task mon_post_reset(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_mon_c::mon_trn()
    */
   extern task mon_trn(output uvma_obi_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_obi_mon_c::process_trn()
    */
   extern function void process_trn(ref uvma_obi_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_obi_mon_c::send_trn_to_sequencer()
    */
   extern task send_trn_to_sequencer(ref uvma_obi_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_obi_mon_c::check_signals_same()
    */
   extern task check_signals_same(ref uvma_obi_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_obi_mon_c::sample_trn_from_vif()
    */
   extern task sample_trn_from_vif(output uvma_obi_mon_trn_c trn);
   
endclass : uvma_obi_mon_c


function uvma_obi_mon_c::new(string name="uvma_obi_mon", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_mon_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   vif_passive_mp = cntxt.vif.passive_mp;
   
   ap           = new("ap"          , this);
   sequencer_ap = new("sequencer_ap", this);
  
endfunction : build_phase


task uvma_obi_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   fork
      observe_reset();
      
      begin
         forever begin
            wait (cfg.enabled);
            
            fork
               begin
                  case (cntxt.reset_state)
                     UVMA_OBI_RESET_STATE_PRE_RESET : mon_pre_reset (phase);
                     UVMA_OBI_RESET_STATE_IN_RESET  : mon_in_reset  (phase);
                     UVMA_OBI_RESET_STATE_POST_RESET: mon_post_reset(phase);
                  endcase
               end
               
               begin
                  wait (!cfg.enabled);
               end
            join_any
            disable fork;
         end
      end
   join_none
   
endtask : run_phase


task uvma_obi_mon_c::observe_reset();
   
   forever begin
      wait (cfg.enabled);
      
      fork
         begin
            wait (cntxt.vif.reset_n === 0);
            cntxt.reset_state = UVMA_OBI_RESET_STATE_IN_RESET;
            wait (cntxt.vif.reset_n === 1);
            cntxt.reset_state = UVMA_OBI_RESET_STATE_POST_RESET;
         end
         
         begin
            wait (!cfg.enabled);
         end
      join_any
      disable fork;
   end
   
endtask : observe_reset


task uvma_obi_mon_c::mon_pre_reset(uvm_phase phase);
   
   @(vif_passive_mp.mon_cb);
   
endtask : mon_pre_reset


task uvma_obi_mon_c::mon_in_reset(uvm_phase phase);
   
   @(vif_passive_mp.mon_cb);
   
endtask : mon_in_reset


task uvma_obi_mon_c::mon_post_reset(uvm_phase phase);
   
   uvma_obi_mon_trn_c  trn;
   
   mon_trn(trn);
   `uvm_info("OBI_MON", $sformatf("monitored transaction:\n%s", trn.sprint()), UVM_MEDIUM/*HIGH*/)
   process_trn(trn);
   ap.write   (trn);
   `uvml_hrtbt()
   
endtask : mon_post_reset


task uvma_obi_mon_c::mon_trn(output uvma_obi_mon_trn_c trn);
   
   realtime  trn_start;
   
   cntxt.mon_gnt_latency    = 0;
   cntxt.mon_rvalid_latency = 0;
   cntxt.mon_rready_latency = 0;
   cntxt.mon_rp_hold        = 0;
   
   // Wait for req
   while (vif_passive_mp.mon_cb.req !== 1'b1) begin
      @(vif_passive_mp.mon_cb);
   end
   trn_start = $realtime();
   
   // Address phase
   sample_trn_from_vif(trn);
   if (cfg.enabled && cfg.is_active && (cfg.drv_mode == UVMA_OBI_MODE_SLV)) begin
      send_trn_to_sequencer(trn);
   end
   
   // Wait for gnt
   while (vif_passive_mp.mon_cb.gnt !== 1'b1) begin
      @(vif_passive_mp.mon_cb);
      // TODO Check that trn's fields haven't changed
      cntxt.mon_gnt_latency++;
   end
   
   // Wait for rvalid
   while (vif_passive_mp.mon_cb.rvalid !== 1'b1) begin
      @(vif_passive_mp.mon_cb);
      // TODO Check that trn's fields haven't changed
      cntxt.mon_rvalid_latency++;
   end
   
   // Wait for rready
   while ((vif_passive_mp.mon_cb.rvalid === 1'b1) && (vif_passive_mp.mon_cb.rready !== 1'b1)) begin
      @(vif_passive_mp.mon_cb);
      sample_trn_from_vif(trn);
      // TODO Check that trn's fields haven't changed
      cntxt.mon_rready_latency++;
   end
   
   // Response phase
   while ((vif_passive_mp.mon_cb.rvalid === 1'b1) && (vif_passive_mp.mon_cb.rready === 1'b1) && (vif_passive_mp.mon_cb.req === 1'b0)) begin
      sample_trn_from_vif(trn);
      // TODO Check that trn's fields haven't changed
      @(vif_passive_mp.mon_cb);
      cntxt.mon_rp_hold++;
   end
   trn.__timestamp_start = trn_start;
   
endtask : mon_trn


function void uvma_obi_mon_c::process_trn(ref uvma_obi_mon_trn_c trn);
   
   trn.auser_width = cfg.auser_width;
   trn.wuser_width = cfg.wuser_width;
   trn.ruser_width = cfg.ruser_width;
   trn.addr_width  = cfg.addr_width ;
   trn.data_width  = cfg.data_width ;
   trn.id_width    = cfg.id_width   ;
   
   trn.gnt_latency    = cntxt.mon_gnt_latency   ;
   trn.rvalid_latency = cntxt.mon_rvalid_latency;
   trn.rready_latency = cntxt.mon_rready_latency;
   trn.rp_hold        = cntxt.mon_rp_hold       ;
   
endfunction : process_trn


task uvma_obi_mon_c::send_trn_to_sequencer(ref uvma_obi_mon_trn_c trn);
   
   sequencer_ap.write(trn);
   
endtask : send_trn_to_sequencer


task uvma_obi_mon_c::check_signals_same(ref uvma_obi_mon_trn_c trn);
   
   uvma_obi_mon_trn_c  new_trn;
   sample_trn_from_vif(new_trn);
   
   if (!trn.compare(new_trn)) begin
      //`uvm_error("OBI_MON", "Signal(s) changed during access")
      trn.__has_error = 1;
   end
   
endtask : check_signals_same


task uvma_obi_mon_c::sample_trn_from_vif(output uvma_obi_mon_trn_c trn);
   
   trn = uvma_obi_mon_trn_c::type_id::create("trn");
   trn.__originator = this.get_full_name();
   
   if (vif_passive_mp.mon_cb.we === 1'b1) begin
      trn.access_type = UVMA_OBI_ACCESS_WRITE;
   end
   else if (vif_passive_mp.mon_cb.we === 1'b0) begin
      trn.access_type = UVMA_OBI_ACCESS_READ;
   end
   else begin
      `uvm_error("OBI_MON", $sformatf("Invalid value for we:%b", vif_passive_mp.mon_cb.we))
      trn.__has_error = 1;
   end
   
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      trn.address[ii] = vif_passive_mp.mon_cb.addr[ii];
   end
   for (int unsigned ii=0; ii<(cfg.data_width/8); ii++) begin
      trn.be[ii] = vif_passive_mp.mon_cb.be[ii];
   end
   for (int unsigned ii=0; ii<cfg.auser_width; ii++) begin
      trn.auser[ii] = vif_passive_mp.mon_cb.auser[ii];
   end
   for (int unsigned ii=0; ii<cfg.wuser_width; ii++) begin
      trn.wuser[ii] = vif_passive_mp.mon_cb.wuser[ii];
   end
   for (int unsigned ii=0; ii<cfg.ruser_width; ii++) begin
      trn.ruser[ii] = vif_passive_mp.mon_cb.ruser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      trn.id[ii] = vif_passive_mp.mon_cb.rid[ii];
   end
   
   if (trn.access_type == UVMA_OBI_ACCESS_WRITE) begin
      for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
         trn.data[ii] = vif_passive_mp.mon_cb.wdata[ii];
      end
   end
   else if (trn.access_type == UVMA_OBI_ACCESS_READ) begin
      for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
         trn.data[ii] = vif_passive_mp.mon_cb.rdata[ii];
      end
   end
   else begin
      `uvm_error("OBI_MON", $sformatf("Invalid value for access_type:%d", trn.access_type))
      trn.__has_error = 1;
   end
   
endtask : sample_trn_from_vif


`endif // __UVMA_OBI_MON_SV__
