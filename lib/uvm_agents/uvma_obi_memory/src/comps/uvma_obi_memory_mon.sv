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


`ifndef __UVMA_OBI_MEMORY_MON_SV__
`define __UVMA_OBI_MEMORY_MON_SV__


/**
 * Component sampling transactions from a Open Bus Interface virtual interface
 * (uvma_obi_if).
 */
class uvma_obi_memory_mon_c extends uvm_monitor;
   
   // Objects
   uvma_obi_memory_cfg_c    cfg;
   uvma_obi_memory_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port#(uvma_obi_memory_mon_trn_c)  ap;
   uvm_analysis_port#(uvma_obi_memory_mon_trn_c)  sequencer_ap;
   
   // Handles to virtual interface modport
   virtual uvma_obi_memory_if.passive_mp  passive_mp;
   
   
   `uvm_component_utils_begin(uvma_obi_memory_mon_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_mon", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_memory_mon_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Monitors passive_mp for asynchronous reset and updates the context's reset state.
    */
   extern task observe_reset();
   
   /**
    * TODO Describe uvma_obi_memory_mon_c::mon_chan_a_pre_reset/mon_chan_a_in_reset/mon_chan_a_post_reset()
    */
   extern task mon_chan_a_pre_reset ();
   extern task mon_chan_a_in_reset  ();
   extern task mon_chan_a_post_reset();
   
   /**
    * TODO Describe uvma_obi_memory_mon_c::mon_chan_r_pre_reset/mon_chan_r_in_reset/mon_chan_r_post_reset()
    */
   extern task mon_chan_r_pre_reset ();
   extern task mon_chan_r_in_reset  ();
   extern task mon_chan_r_post_reset();
   
   /**
    * TODO Describe uvma_obi_memory_mon_c::mon_chan_a_trn()
    */
   extern task mon_chan_a_trn(output uvma_obi_memory_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_obi_memory_mon_c::mon_chan_r_trn()
    */
   extern task mon_chan_r_trn(output uvma_obi_memory_mon_trn_c trn);
   
   /**
    * User hooks for modifying transactions after they've been sampled but before they're sent out the analysis port(s).
    */
   extern virtual function void process_a_trn(ref uvma_obi_memory_mon_trn_c trn);
   extern virtual function void process_r_trn(ref uvma_obi_memory_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_obi_memory_mon_c::send_trn_to_sequencer()
    */
   extern task send_trn_to_sequencer(ref uvma_obi_memory_mon_trn_c trn);
   
   /**
    * TODO Describe uvma_obi_memory_mon_c::sample_trn_a_from_vif()
    */
   extern task sample_trn_a_from_vif(ref uvma_obi_memory_mon_trn_c trn);
   extern task sample_trn_r_from_vif(ref uvma_obi_memory_mon_trn_c trn);
   
endclass : uvma_obi_memory_mon_c


function uvma_obi_memory_mon_c::new(string name="uvma_obi_memory_mon", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_memory_mon_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_memory_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(uvma_obi_memory_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   passive_mp = cntxt.vif.passive_mp;
   
   ap           = new("ap"          , this);
   sequencer_ap = new("sequencer_ap", this);
  
endfunction : build_phase


task uvma_obi_memory_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   if (cfg.enabled) begin
      fork
         observe_reset();
         
         begin : chan_a
            forever begin
               case (cntxt.reset_state)
                  UVMA_OBI_MEMORY_RESET_STATE_PRE_RESET : mon_chan_a_pre_reset ();
                  UVMA_OBI_MEMORY_RESET_STATE_IN_RESET  : mon_chan_a_in_reset  ();
                  UVMA_OBI_MEMORY_RESET_STATE_POST_RESET: mon_chan_a_post_reset();
               endcase
            end
         end
         
         begin : chan_r
            forever begin
               case (cntxt.reset_state)
                  UVMA_OBI_MEMORY_RESET_STATE_PRE_RESET : mon_chan_r_pre_reset ();
                  UVMA_OBI_MEMORY_RESET_STATE_IN_RESET  : mon_chan_r_in_reset  ();
                  UVMA_OBI_MEMORY_RESET_STATE_POST_RESET: mon_chan_r_post_reset();
               endcase
            end
         end
      join_none
   end
   
endtask : run_phase


task uvma_obi_memory_mon_c::observe_reset();
   
   forever begin
      wait (cntxt.vif.reset_n === 0);
      cntxt.reset_state = UVMA_OBI_MEMORY_RESET_STATE_IN_RESET;
      `uvm_info("OBI_MEMORY_MON", $sformatf("RESET_STATE_IN_RESET"), UVM_NONE)
      wait (cntxt.vif.reset_n === 1);
      cntxt.reset_state = UVMA_OBI_MEMORY_RESET_STATE_POST_RESET;
      `uvm_info("OBI_MEMORY_MON", $sformatf("RESET_STATE_POST_RESET"), UVM_NONE)
   end
   
endtask : observe_reset


task uvma_obi_memory_mon_c::mon_chan_a_pre_reset();
   
   @(passive_mp.mon_cb);
   
endtask : mon_chan_a_pre_reset


task uvma_obi_memory_mon_c::mon_chan_a_in_reset();
   
   @(passive_mp.mon_cb);
   
endtask : mon_chan_a_in_reset


task uvma_obi_memory_mon_c::mon_chan_a_post_reset();
   
   uvma_obi_memory_mon_trn_c  trn;
   
   mon_chan_a_trn(trn);
   trn.cfg = cfg;
   cntxt.mon_outstanding_reads_q.push_back(trn);
   `uvm_info("OBI_MEMORY_MON", $sformatf("monitored transaction on channel A:\n%s", trn.sprint()), UVM_HIGH)
   process_a_trn(trn);
   `uvm_info("OBI_MEMORY_MON", $sformatf("monitored transaction on channel A after process_a_trn():\n%s", trn.sprint()), UVM_HIGH)
   
   if (cfg.enabled && cfg.is_active && (cfg.drv_mode == UVMA_OBI_MEMORY_MODE_SLV)) begin
      send_trn_to_sequencer(trn);
      `uvm_info("OBI_MEMORY_MON", $sformatf("Sent trn to sequencer"), UVM_HIGH)
   end
   `uvml_hrtbt()
   @(passive_mp.mon_cb);

endtask : mon_chan_a_post_reset


task uvma_obi_memory_mon_c::mon_chan_r_pre_reset();
   
   @(passive_mp.mon_cb);
   
endtask : mon_chan_r_pre_reset


task uvma_obi_memory_mon_c::mon_chan_r_in_reset();
   
   @(passive_mp.mon_cb);
   
endtask : mon_chan_r_in_reset


task uvma_obi_memory_mon_c::mon_chan_r_post_reset();
   
   uvma_obi_memory_mon_trn_c  trn;
   
   mon_chan_r_trn(trn);
   trn.cfg = cfg;
   `uvm_info("OBI_MEMORY_MON", $sformatf("monitored transaction on channel R:\n%s", trn.sprint()), UVM_HIGH)
   process_r_trn(trn);
   `uvm_info("OBI_MEMORY_MON", $sformatf("monitored transaction on channel R after process_r_trn():\n%s", trn.sprint()), UVM_HIGH)
   ap.write(trn);
   `uvml_hrtbt()
   @(passive_mp.mon_cb);

endtask : mon_chan_r_post_reset


task uvma_obi_memory_mon_c::mon_chan_a_trn(output uvma_obi_memory_mon_trn_c trn);
   
   trn = uvma_obi_memory_mon_trn_c::type_id::create("trn");
   
   while((passive_mp.mon_cb.req !== 1'b1) || (passive_mp.mon_cb.gnt !== 1'b1)) begin
      @(passive_mp.mon_cb);
      trn.gnt_latency++;
   end
   
   sample_trn_a_from_vif(trn);
   trn.__timestamp_start = $realtime();   
   
endtask : mon_chan_a_trn


task uvma_obi_memory_mon_c::mon_chan_r_trn(output uvma_obi_memory_mon_trn_c trn);
   
   uvma_obi_memory_mon_trn_c  trn_a;
   
   trn = uvma_obi_memory_mon_trn_c::type_id::create("trn");
   
   while ((passive_mp.mon_cb.rvalid !== 1'b1) && (passive_mp.mon_cb.rready !== 1'b1)) begin
      @(passive_mp.mon_cb);
      trn.rvalid_latency++;
   end
   
   sample_trn_r_from_vif(trn);
   trn.__timestamp_end = $realtime();
   if (cntxt.mon_outstanding_reads_q.size()) begin
      trn_a = cntxt.mon_outstanding_reads_q.pop_front();
      trn.__timestamp_start = trn_a.__timestamp_start;
      trn.address = trn_a.address;
   end
   else begin
      `uvm_error("OBI_MON", $sformatf("No outstanding read for observed rvalid assertion:\n%s", trn.sprint()))
   end   
   
endtask : mon_chan_r_trn


function void uvma_obi_memory_mon_c::process_a_trn(ref uvma_obi_memory_mon_trn_c trn);
   
   
endfunction : process_a_trn


function void uvma_obi_memory_mon_c::process_r_trn(ref uvma_obi_memory_mon_trn_c trn);
   
   
endfunction : process_r_trn


task uvma_obi_memory_mon_c::send_trn_to_sequencer(ref uvma_obi_memory_mon_trn_c trn);
   
   sequencer_ap.write(trn);
   
endtask : send_trn_to_sequencer


task uvma_obi_memory_mon_c::sample_trn_a_from_vif(ref uvma_obi_memory_mon_trn_c trn);
   
   trn.__originator = this.get_full_name();
   
   if (passive_mp.mon_cb.we === 1'b1) begin
      trn.access_type = UVMA_OBI_MEMORY_ACCESS_WRITE;
   end
   else if (passive_mp.mon_cb.we === 1'b0) begin
      trn.access_type = UVMA_OBI_MEMORY_ACCESS_READ;
   end
   else begin
      `uvm_error("OBI_MEMORY_MON", $sformatf("Invalid value for we:%b", passive_mp.mon_cb.we))
      trn.__has_error = 1;
   end
   
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      trn.address[ii] = passive_mp.mon_cb.addr[ii];
   end
   for (int unsigned ii=0; ii<(cfg.data_width/8); ii++) begin
      trn.be[ii] = passive_mp.mon_cb.be[ii];
   end
   for (int unsigned ii=0; ii<cfg.auser_width; ii++) begin
      trn.auser[ii] = passive_mp.mon_cb.auser[ii];
   end
   for (int unsigned ii=0; ii<cfg.wuser_width; ii++) begin
      trn.wuser[ii] = passive_mp.mon_cb.wuser[ii];
   end
   for (int unsigned ii=0; ii<cfg.ruser_width; ii++) begin
      trn.ruser[ii] = passive_mp.mon_cb.ruser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      trn.id[ii] = passive_mp.mon_cb.rid[ii];
   end
   
   if (trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
         trn.data[ii] = passive_mp.mon_cb.wdata[ii];
      end
   end
   else if (trn.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
         trn.data[ii] = passive_mp.mon_cb.rdata[ii];
      end
   end
   else begin
      `uvm_error("OBI_MEMORY_MON", $sformatf("Invalid value for access_type:%d", trn.access_type))
      trn.__has_error = 1;
   end
   
endtask : sample_trn_a_from_vif


task uvma_obi_memory_mon_c::sample_trn_r_from_vif(ref uvma_obi_memory_mon_trn_c trn);
   
   trn.__originator = this.get_full_name();
   
   if (passive_mp.mon_cb.we === 1'b1) begin
      trn.access_type = UVMA_OBI_MEMORY_ACCESS_WRITE;
   end
   else if (passive_mp.mon_cb.we === 1'b0) begin
      trn.access_type = UVMA_OBI_MEMORY_ACCESS_READ;
   end
   else begin
      `uvm_error("OBI_MEMORY_MON", $sformatf("Invalid value for we:%b", passive_mp.mon_cb.we))
      trn.__has_error = 1;
   end
   
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      trn.address[ii] = passive_mp.mon_cb.addr[ii];
   end
   for (int unsigned ii=0; ii<(cfg.data_width/8); ii++) begin
      trn.be[ii] = passive_mp.mon_cb.be[ii];
   end
   for (int unsigned ii=0; ii<cfg.auser_width; ii++) begin
      trn.auser[ii] = passive_mp.mon_cb.auser[ii];
   end
   for (int unsigned ii=0; ii<cfg.wuser_width; ii++) begin
      trn.wuser[ii] = passive_mp.mon_cb.wuser[ii];
   end
   for (int unsigned ii=0; ii<cfg.ruser_width; ii++) begin
      trn.ruser[ii] = passive_mp.mon_cb.ruser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      trn.id[ii] = passive_mp.mon_cb.rid[ii];
   end
   
   if (trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
         trn.data[ii] = passive_mp.mon_cb.wdata[ii];
      end
   end
   else if (trn.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
         trn.data[ii] = passive_mp.mon_cb.rdata[ii];
      end
   end
   else begin
      `uvm_error("OBI_MEMORY_MON", $sformatf("Invalid value for access_type:%d", trn.access_type))
      trn.__has_error = 1;
   end
   
endtask : sample_trn_r_from_vif


`endif // __UVMA_OBI_MEMORY_MON_SV__
