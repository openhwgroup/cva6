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


`ifndef __UVMA_OBI_MON_SV__
`define __UVMA_OBI_MON_SV__


/**
 * Component sampling transactions from an Open Bus Interface (uvma_obi_if).
 */
class uvma_obi_mon_c extends uvm_monitor;
   
   virtual uvma_obi_if.mon_a_mp  mp_a; ///< Handle to A modport
   virtual uvma_obi_if.mon_r_mp  mp_r; ///< Handle to R modport
   
   // Objects
   uvma_obi_cfg_c    cfg  ; ///< Agent configuration handle
   uvma_obi_cntxt_c  cntxt; ///< Agent context handle
   
   // TLM
   uvm_analysis_port#(uvma_obi_mstr_a_mon_trn_c)  mstr_a_ap; ///< TODO Describe uvma_obi_mon_c::mstr_a_ap
   uvm_analysis_port#(uvma_obi_mstr_r_mon_trn_c)  mstr_r_ap; ///< TODO Describe uvma_obi_mon_c::mstr_r_ap
   uvm_analysis_port#(uvma_obi_slv_a_mon_trn_c )  slv_a_ap ; ///< TODO Describe uvma_obi_mon_c::slv_a_ap
   uvm_analysis_port#(uvma_obi_slv_r_mon_trn_c )  slv_r_ap ; ///< TODO Describe uvma_obi_mon_c::slv_r_ap
   
   
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
    * Oversees monitoring, depending on the reset state, by calling mon_<pre|in|post>_reset() tasks.
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Updates the context's reset state.
    */
   extern virtual task observe_reset();
   
   /**
    * Synchronous reset thread.
    */
   extern virtual task observe_reset_sync();
   
   /**
    * Asynchronous reset thread.
    */
   extern virtual task observe_reset_async();
   
   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern virtual task mon_mstr_a_post_reset();
   
   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern virtual task mon_slv_r_post_reset();
   
   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern virtual task mon_slv_a_post_reset();
   
   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern virtual task mon_slv_r_post_reset();
   
   /**
    * Creates trn by sampling the virtual interface's (cntxt.vif) signals.
    */
   extern virtual task sample_mstr_a_trn(output uvma_obi_mstr_a_mon_trn_c trn);
   
   /**
    * Creates trn by sampling the virtual interface's (cntxt.vif) signals.
    */
   extern virtual task sample_mstr_r_trn(output uvma_obi_mstr_r_mon_trn_c trn);
   
   /**
    * Creates trn by sampling the virtual interface's (cntxt.vif) signals.
    */
   extern virtual task sample_slv_a_trn(output uvma_obi_slv_a_mon_trn_c trn);
   
   /**
    * Creates trn by sampling the virtual interface's (cntxt.vif) signals.
    */
   extern virtual task sample_slv_r_trn(output uvma_obi_slv_r_mon_trn_c trn);
   
   /**
    * Appends cfg, prints out trn and issues heartbeat.
    */
   extern virtual function void process_mstr_a_trn(ref uvma_obi_mstr_a_mon_trn_c trn);
   
   /**
    * Appends cfg, prints out trn and issues heartbeat.
    */
   extern virtual function void process_mstr_r_trn(ref uvma_obi_mstr_r_mon_trn_c trn);
   
   /**
    * Appends cfg, prints out trn and issues heartbeat.
    */
   extern virtual function void process_slv_a_trn(ref uvma_obi_slv_a_mon_trn_c trn);
   
   /**
    * Appends cfg, prints out trn and issues heartbeat.
    */
   extern virtual function void process_slv_r_trn(ref uvma_obi_slv_r_mon_trn_c trn);
   
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
   
   ap = new("ap", this);
   mp_a = cntxt.vif.mon_a_mp;
   mp_r = cntxt.vif.mon_r_mp;
  
endfunction : build_phase


task uvma_obi_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   if (cfg.enabled) begin
      fork
         observe_reset();
         
         begin : mstr_a
            forever begin
               case (cntxt.reset_state)
                  UVML_RESET_STATE_PRE_RESET : @(mp_a.mon_a_cb);
                  UVML_RESET_STATE_IN_RESET  : @(mp_a.mon_a_cb);
                  UVML_RESET_STATE_POST_RESET: mon_mstr_a_post_reset();
               endcase
            end
         end
         
         begin : mstr_r
            forever begin
               case (cntxt.reset_state)
                  UVML_RESET_STATE_PRE_RESET : @(mp_r.mon_r_cb);
                  UVML_RESET_STATE_IN_RESET  : @(mp_r.mon_r_cb);
                  UVML_RESET_STATE_POST_RESET: mon_mstr_r_post_reset();
               endcase
            end
         end
         
         begin : slv_a
            forever begin
               case (cntxt.reset_state)
                  UVML_RESET_STATE_PRE_RESET : @(mp_a.mon_a_cb);
                  UVML_RESET_STATE_IN_RESET  : @(mp_a.mon_a_cb);
                  UVML_RESET_STATE_POST_RESET: mon_slv_a_post_reset();
               endcase
            end
         end
         
         begin : slv_r
            forever begin
               case (cntxt.reset_state)
                  UVML_RESET_STATE_PRE_RESET : @(mp_r.mon_r_cb);
                  UVML_RESET_STATE_IN_RESET  : @(mp_r.mon_r_cb);
                  UVML_RESET_STATE_POST_RESET: mon_slv_r_post_reset();
               endcase
            end
         end
      join_none
   end
   
endtask : run_phase


task uvma_obi_mon_c::observe_reset();
   
   case (cfg.reset_mode)
      UVML_RESET_MODE_SYNCHRONOUS : observe_reset_sync ();
      UVML_RESET_MODE_ASYNCHRONOUS: observe_reset_async();
      
      default: begin
         `uvm_fatal("OBI_MON", $sformatf("Illegal cfg.reset_mode: %s", cfg.reset_mode.name()))
      end
   endcase
   
endtask : observe_reset


task uvma_obi_mon_c::observe_reset_sync();
   
   forever begin
      while (cntxt.vif.reset_n !== 1'b0) begin
         wait (cntxt.vif.clk === 1);
         wait (cntxt.vif.clk === 0);
      end
      cntxt.reset_state = UVML_RESET_STATE_IN_RESET;
      `uvm_info("OBI_MON", "Entered IN_RESET state", UVM_MEDIUM)
      
      while (cntxt.vif.reset_n !== 1'b1) begin
         wait (cntxt.vif.clk === 1);
         wait (cntxt.vif.clk === 0);
      end
      cntxt.reset_state = UVML_RESET_STATE_POST_RESET;
      `uvm_info("OBI_MON", "Entered POST_RESET state", UVM_MEDIUM)
   end
   
endtask : observe_reset_sync


task uvma_obi_mon_c::observe_reset_async();
   
   forever begin
      wait (cntxt.vif.reset_n === 0);
      cntxt.reset_state = UVML_RESET_STATE_IN_RESET;
      `uvm_info("OBI_MON", "Entered IN_RESET state", UVM_MEDIUM)
      
      wait (cntxt.vif.reset_n === 1);
      cntxt.reset_state = UVML_RESET_STATE_POST_RESET;
      `uvm_info("OBI_MON", "Entered POST_RESET state", UVM_MEDIUM)
   end
   
endtask : observe_reset_async


task uvma_obi_mon_c::mon_mstr_a_post_reset();
   
   uvma_obi_mstr_a_mon_trn_c  trn;
   
   sample_mstr_a_trn (trn);
   process_mstr_a_trn(trn);
   mstr_a_ap.write   (trn);
   
endtask : mon_mstr_a_post_reset


task uvma_obi_mon_c::mon_mstr_r_post_reset();
   
   uvma_obi_mstr_r_mon_trn_c  trn;
   
   sample_mstr_r_trn (trn);
   process_mstr_r_trn(trn);
   mstr_r_ap.write   (trn);
   
endtask : mon_mstr_r_post_reset


task uvma_obi_mon_c::mon_slv_a_post_reset();
   
   uvma_obi_slv_a_mon_trn_c  trn;
   
   sample_slv_a_trn (trn);
   process_slv_a_trn(trn);
   slv_a_ap.write   (trn);
   
endtask : mon_slv_a_post_reset


task uvma_obi_mon_c::mon_slv_r_post_reset();
   
   uvma_obi_slv_r_mon_trn_c  trn;
   
   sample_slv_r_trn (trn);
   process_slv_r_trn(trn);
   slv_r_ap.write   (trn);
   
endtask : mon_slv_r_post_reset


task uvma_obi_mon_c::sample_mstr_a_trn(output uvma_obi_mstr_a_mon_trn_c trn);
   
   @(mp_a.mon_a_cb);
   `uvm_info("OBI_MON", "Sampling MSTR Channel A transaction", UVM_DEBUG)
   trn = uvma_obi_mstr_a_mon_trn_c::type_id::create("trn");
   trn.req       = mp_a.mon_a_cb.gnt    ;
   trn.we        = mp_a.mon_a_cb.we     ;
   trn.atop      = mp_a.mon_a_cb.atop   ;
   trn.memtype   = mp_a.mon_a_cb.memtype;
   trn.prot      = mp_a.mon_a_cb.prot   ;
   trn.reqpar    = mp_a.mon_a_cb.reqpar ;
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      trn.addr[ii] = mp_a.mon_a_cb.addr[ii];
   end
   for (int unsigned ii=0; ii<(cfg.data_width/8); ii++) begin
      trn.be[ii] = mp_a.mon_a_cb.be[ii];
   end
   for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
      trn.wdata[ii] = mp_a.mon_a_cb.wdata[ii];
   end
   for (int unsigned ii=0; ii<cfg.auser_width; ii++) begin
      trn.auser[ii] = mp_a.mon_a_cb.auser[ii];
   end
   for (int unsigned ii=0; ii<cfg.wuser_width; ii++) begin
      trn.wuser[ii] = mp_a.mon_a_cb.wuser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      trn.aid[ii] = mp_a.mon_a_cb.aid[ii];
   end
   for (int unsigned ii=0; ii<cfg.achk_width; ii++) begin
      trn.achk[ii] = mp_a.mon_a_cb.achk[ii];
   end
   
   wait (mp_a.clk === 1'b0);
   
endtask : sample_mstr_a_trn


task uvma_obi_mon_c::sample_mstr_r_trn(output uvma_obi_mstr_r_mon_trn_c trn);
   
   @(mp_r.mon_r_cb);
   `uvm_info("OBI_MON", "Sampling MSTR Channel R transaction", UVM_HIGH)
   trn = uvma_obi_mstr_r_mon_trn_c::type_id::create("trn");
   trn.req       = mp_a.mon_a_cb.gnt;
   trn.rreadypar = mp_r.mon_r_cb.rreadypar;
   
   wait (mp_r.clk === 1'b0);
   
endtask : sample_mstr_r_trn


task uvma_obi_mon_c::sample_slv_a_trn(output uvma_obi_slv_a_mon_trn_c trn);
   
   @(mp_a.mon_a_cb);
   `uvm_info("OBI_MON", "Sampling SLV Channel A transaction", UVM_DEBUG)
   trn = uvma_obi_slv_a_mon_trn_c::type_id::create("trn");
   trn.gnt    = mp_a.mon_a_cb.gnt;
   trn.gntpar = mp_a.mon_a_cb.gntpar;
   
   wait (mp_a.clk === 1'b0);
   
endtask : sample_slv_a_trn


task uvma_obi_mon_c::sample_slv_r_trn(output uvma_obi_slv_r_mon_trn_c trn);
   
   @(mp_r.mon_r_cb);
   `uvm_info("OBI_MON", "Sampling SLV Channel R transaction", UVM_DEBUG)
   trn = uvma_obi_slv_r_mon_trn_c::type_id::create("trn");
   trn.rvalid    = mp_r.mon_r_cb.rvalid   ;
   trn.rvalidpar = mp_r.mon_r_cb.rvalidpar;
   trn.err       = mp_r.mon_r_cb.err      ;
   trn.exokay    = mp_r.mon_r_cb.exokay   ;
   for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
      trn.rdata[ii] = mp_r.mon_r_cb.rdata[ii];
   end
   for (int unsigned ii=0; ii<cfg.ruser_width; ii++) begin
      trn.ruser[ii] = mp_a.mon_a_cb.ruser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      trn.rid[ii] = mp_a.mon_a_cb.rid[ii];
   end
   for (int unsigned ii=0; ii<cfg.rchk_width; ii++) begin
      trn.rchk[ii] = mp_a.mon_a_cb.rchk[ii];
   end
   
   wait (mp_r.clk === 1'b0);
   
endtask : sample_slv_r_trn


function void uvma_obi_mon_c::process_mstr_a_trn(ref uvma_obi_mstr_a_mon_trn_c trn);
   
   trn.cfg = cfg;
   trn.set_initiator(this);
   trn.set_timestamp_end($realtime());
   `uvm_info("OBI_MON", $sformatf("Sampled MSTR channel A transaction from the virtual interface:\n%s", trn.sprint()), UVM_HIGH)
   
endfunction : process_mstr_a_trn


function void uvma_obi_mon_c::process_mstr_r_trn(ref uvma_obi_mstr_r_mon_trn_c trn);
   
   trn.cfg = cfg;
   trn.set_initiator(this);
   trn.set_timestamp_end($realtime());
   `uvm_info("OBI_MON", $sformatf("Sampled MSTR channel R transaction from the virtual interface:\n%s", trn.sprint()), UVM_HIGH)
   
endfunction : process_mstr_r_trn


function void uvma_obi_mon_c::process_slv_a_trn(ref uvma_obi_slv_a_mon_trn_c trn);
   
   trn.cfg = cfg;
   trn.set_initiator(this);
   trn.set_timestamp_end($realtime());
   `uvm_info("OBI_MON", $sformatf("Sampled SLV channel A transaction from the virtual interface:\n%s", trn.sprint()), UVM_HIGH)
   
endfunction : process_slv_a_trn


function void uvma_obi_mon_c::process_slv_r_trn(ref uvma_obi_slv_r_mon_trn_c trn);
   
   trn.cfg = cfg;
   trn.set_initiator(this);
   trn.set_timestamp_end($realtime());
   `uvm_info("OBI_MON", $sformatf("Sampled SLV channel R transaction from the virtual interface:\n%s", trn.sprint()), UVM_HIGH)
   
endfunction : process_slv_r_trn


`endif // __UVMA_OBI_MON_SV__
