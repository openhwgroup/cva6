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


`ifndef __UVMA_OBI_DRV_SV__
`define __UVMA_OBI_DRV_SV__


/**
 * Component driving a Open Bus Interface virtual interface (uvma_obi_if).
 * @note The req & rsp's roles are switched when this driver is in 'slv' mode.
 * @todo Move implementation to a sequence-based approach
 */
class uvma_obi_drv_c extends uvm_driver#(
   .REQ(uvma_obi_base_seq_item_c),
   .RSP(uvma_obi_mon_trn_c      )
);
   
   // Objects
   uvma_obi_cfg_c    cfg;
   uvma_obi_cntxt_c  cntxt;
   
   // TLM
   uvm_analysis_port     #(uvma_obi_mstr_seq_item_c)  mstr_ap;
   uvm_analysis_port     #(uvma_obi_slv_seq_item_c )  slv_ap ;
   uvm_tlm_analysis_fifo #(uvma_obi_mon_trn_c      )  mon_trn_fifo;
   
   // Handles to virtual interface modports
   virtual uvma_obi_if.active_mstr_mp  vif_mstr_mp;
   virtual uvma_obi_if.active_slv_mp   vif_slv_mp ;
   
   
   `uvm_component_utils_begin(uvma_obi_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_drv", uvm_component parent=null);
   
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
    * Called by run_phase() while agent is in pre-reset state.
    */
   extern task drv_pre_reset(uvm_phase phase);
   
   /**
    * Called by run_phase() while agent is in reset state.
    */
   extern task drv_in_reset(uvm_phase phase);
   
   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern task drv_post_reset(uvm_phase phase);
   
   /**
    * TODO Describe uvma_obi_drv::get_next_item()
    */
   extern task get_next_item(output uvma_obi_base_seq_item_c req);
   
   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern task drv_mstr_req(ref uvma_obi_mstr_seq_item_c req);
   
   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern task drv_mstr_read_req(ref uvma_obi_mstr_seq_item_c req);
   
   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern task drv_mstr_write_req(ref uvma_obi_mstr_seq_item_c req);
   
   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern task drv_slv_req(ref uvma_obi_slv_seq_item_c req);
   
   /**
    * Drives the interface's signals using req's contents.
    */
   extern virtual task drv_slv_read_req(ref uvma_obi_slv_seq_item_c req);
   
   /**
    * Drives the interface's signals using req's contents.
    */
   extern virtual task drv_slv_write_req(ref uvma_obi_slv_seq_item_c req);
   
   /**
    * TODO Describe uvma_obi_drv_c::wait_for_rsp()
    */
   extern task wait_for_rsp(output uvma_obi_mon_trn_c rsp);
   
   /**
    * TODO Describe uvma_obi_drv_c::process_mstr_rsp()
    */
   extern task process_mstr_rsp(ref uvma_obi_mstr_seq_item_c req, ref uvma_obi_mon_trn_c rsp);
   
   /**
    * TODO Describe uvma_obi_drv_c::process_slv_rsp()
    */
   extern task process_slv_rsp(ref uvma_obi_slv_seq_item_c rsp, ref uvma_obi_mon_trn_c req);
   
   /**
    * TODO Describe uvma_obi_drv_c::drv_mstr_idle()
    */
   extern task drv_mstr_idle();
   
   /**
    * TODO Describe uvma_obi_drv_c::drv_slv_idle()
    */
   extern task drv_slv_idle();
   
endclass : uvma_obi_drv_c


function uvma_obi_drv_c::new(string name="uvma_obi_drv", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_drv_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_obi_cfg_c)::set(this, "*", "cfg", cfg);
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_obi_cntxt_c)::set(this, "*", "cntxt", cntxt);
   vif_mstr_mp = cntxt.vif.active_mstr_mp;
   vif_slv_mp  = cntxt.vif.active_slv_mp ;
   
   mstr_ap      = new("mstr_ap"     , this);
   slv_ap       = new("slv_ap"      , this);
   mon_trn_fifo = new("mon_trn_fifo", this);
   
endfunction : build_phase


task uvma_obi_drv_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   forever begin
      wait (cfg.enabled && cfg.is_active);
      
      fork
         begin
            case (cntxt.reset_state)
               UVMA_OBI_RESET_STATE_PRE_RESET : drv_pre_reset (phase);
               UVMA_OBI_RESET_STATE_IN_RESET  : drv_in_reset  (phase);
               UVMA_OBI_RESET_STATE_POST_RESET: drv_post_reset(phase);
               
               default: `uvm_fatal("OBI_DRV", $sformatf("Invalid reset_state: %0d", cntxt.reset_state))
            endcase
         end
         
         begin
            wait (!(cfg.enabled && cfg.is_active));
         end
      join_any
      disable fork;
   end
   
endtask : run_phase


task uvma_obi_drv_c::drv_pre_reset(uvm_phase phase);
   
   case (cfg.drv_mode)
      UVMA_OBI_MODE_MSTR: @(vif_mstr_mp.drv_mstr_cb);
      UVMA_OBI_MODE_SLV : @(vif_slv_mp .drv_slv_cb );
      
      default: `uvm_fatal("OBI_DRV", $sformatf("Invalid drv_mode: %0d", cfg.drv_mode))
   endcase
   
endtask : drv_pre_reset


task uvma_obi_drv_c::drv_in_reset(uvm_phase phase);
   
   case (cfg.drv_mode)
      UVMA_OBI_MODE_MSTR: begin
         @(vif_mstr_mp.drv_mstr_cb);
         drv_mstr_idle();
      end
      
      UVMA_OBI_MODE_SLV : begin
         @(vif_slv_mp.drv_slv_cb);
         drv_slv_idle();
      end
      
      default: `uvm_fatal("OBI_DRV", $sformatf("Invalid drv_mode: %0d", cfg.drv_mode))
   endcase
   
endtask : drv_in_reset


task uvma_obi_drv_c::drv_post_reset(uvm_phase phase);
   
   uvma_obi_mstr_seq_item_c  mstr_req;
   uvma_obi_slv_seq_item_c   slv_req;
   uvma_obi_mon_trn_c        mstr_rsp;
   uvma_obi_mon_trn_c        slv_rsp;
   
   case (cfg.drv_mode)
      UVMA_OBI_MODE_MSTR: begin
         // 1. Get next req from sequence and drive it on the vif
         get_next_item(req);
         if (!$cast(mstr_req, req)) begin
            `uvm_fatal("OBI_DRV", $sformatf("Could not cast 'req' (%s) to 'mstr_req' (%s)", $typename(req), $typename(mstr_req)))
         end
         `uvm_info("OBI_DRV", $sformatf("Got mstr_req:\n%s", mstr_req.sprint()), UVM_MEDIUM/*HIGH*/)
         drv_mstr_req(mstr_req);
         
         // 2. Wait for the monitor to send us the slv's rsp with the results of the req
         wait_for_rsp(slv_rsp);
         process_mstr_rsp(mstr_req, slv_rsp);
         
         // 3. Send out to TLM and tell sequencer we're ready for the next sequence item
         mstr_ap.write(mstr_req);
         seq_item_port.item_done();
      end
      
      UVMA_OBI_MODE_SLV: begin
         // 1. Get next req from sequence to reply to mstr and drive it on the vif
         get_next_item(req);
         if (!$cast(slv_req, req)) begin
            `uvm_fatal("OBI_DRV", $sformatf("Could not cast 'req' (%s) to 'slv_req' (%s)", $typename(req), $typename(slv_req)))
         end
         `uvm_info("OBI_DRV", $sformatf("Got slv_req:\n%s", slv_req.sprint()), UVM_MEDIUM/*HIGH*/)
         drv_slv_req(slv_req);
         
         // 2. Send out to TLM and tell sequencer we're ready for the next sequence item
         wait_for_rsp(slv_rsp);
         process_slv_rsp(slv_req, slv_rsp);
         slv_ap.write(slv_req);
         seq_item_port.item_done();
      end
      
      default: `uvm_fatal("OBI_DRV", $sformatf("Invalid drv_mode: %0d", cfg.drv_mode))
   endcase
   
endtask : drv_post_reset


task uvma_obi_drv_c::get_next_item(output uvma_obi_base_seq_item_c req);
   
   seq_item_port.get_next_item(req);
   `uvml_hrtbt()
   
   // Copy cfg fields
   req.mode        = cfg.drv_mode;
   req.auser_width = cfg.auser_width;
   req.wuser_width = cfg.wuser_width;
   req.ruser_width = cfg.ruser_width;
   req.addr_width  = cfg.addr_width ;
   req.data_width  = cfg.data_width ;
   req.id_width    = cfg.id_width   ;
   
endtask : get_next_item


task uvma_obi_drv_c::drv_mstr_req(ref uvma_obi_mstr_seq_item_c req);
   
   case (req.access_type)
      UVMA_OBI_ACCESS_READ: begin
         drv_mstr_read_req(req);
      end
      
      UVMA_OBI_ACCESS_WRITE: begin
         drv_mstr_write_req(req);
      end
      
      default: `uvm_fatal("OBI_DRV", $sformatf("Invalid access_type: %0d", req.access_type))
   endcase
   
endtask : drv_mstr_req


task uvma_obi_drv_c::drv_mstr_read_req(ref uvma_obi_mstr_seq_item_c req);
   
   // Req Latency cycles
   repeat (req.req_latency) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
   // Address phase
   vif_mstr_mp.drv_mstr_cb.req <= 1'b1;
   vif_mstr_mp.drv_mstr_cb.we  <= req.access_type;
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      vif_mstr_mp.drv_mstr_cb.addr[ii] <= req.address[ii];
   end
   for (int unsigned ii=0; ii<(cfg.data_width/8); ii++) begin
      vif_mstr_mp.drv_mstr_cb.be[ii] <= req.be[ii];
   end
   for (int unsigned ii=0; ii<cfg.auser_width; ii++) begin
      vif_mstr_mp.drv_mstr_cb.auser[ii] <= req.auser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      vif_mstr_mp.drv_mstr_cb.aid[ii] <= req.id[ii];
   end
   
   // Wait for grant
   while (vif_mstr_mp.drv_mstr_cb.gnt !== 1'b1) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
   // Wait for rvalid
   if (vif_mstr_mp.drv_mstr_cb.rvalid !== 1'b1) begin
      while (vif_mstr_mp.drv_mstr_cb.rvalid !== 1'b1) begin
         @(vif_mstr_mp.drv_mstr_cb);
      end
   end
   repeat (req.rready_latency) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
   // Response phase
   vif_mstr_mp.drv_mstr_cb.rready <= 1'b1;
   vif_mstr_mp.drv_mstr_cb.req    <= 1'b0;
   repeat (req.rready_hold) begin
      if (vif_mstr_mp.drv_mstr_cb.rvalid !== 1'b1) begin
         break;
      end
      @(vif_mstr_mp.drv_mstr_cb);
   end
   while (vif_mstr_mp.drv_mstr_cb.rvalid === 1'b1) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
   // Tail
   vif_mstr_mp.drv_mstr_cb.rready <= 1'b0;
   drv_mstr_idle();
   repeat (req.tail_length) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
endtask : drv_mstr_read_req


task uvma_obi_drv_c::drv_mstr_write_req(ref uvma_obi_mstr_seq_item_c req);
   
   // Req Latency cycles
   repeat (req.req_latency) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
   // Address phase
   vif_mstr_mp.drv_mstr_cb.req <= 1'b1;
   vif_mstr_mp.drv_mstr_cb.we  <= req.access_type;
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      vif_mstr_mp.drv_mstr_cb.addr[ii] <= req.address[ii];
   end
   for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
      vif_mstr_mp.drv_mstr_cb.wdata[ii] <= req.wdata[ii];
   end
   for (int unsigned ii=0; ii<(cfg.data_width/8); ii++) begin
      vif_mstr_mp.drv_mstr_cb.be[ii] <= req.be[ii];
   end
   for (int unsigned ii=0; ii<cfg.auser_width; ii++) begin
      vif_mstr_mp.drv_mstr_cb.auser[ii] <= req.auser[ii];
   end
   for (int unsigned ii=0; ii<cfg.wuser_width; ii++) begin
      vif_mstr_mp.drv_mstr_cb.wuser[ii] <= req.wuser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      vif_mstr_mp.drv_mstr_cb.aid[ii] <= req.id[ii];
   end
   
   // Wait for grant
   while (vif_mstr_mp.drv_mstr_cb.gnt !== 1'b1) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
   // Wait for rvalid
   while (vif_mstr_mp.drv_mstr_cb.rvalid !== 1'b1) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   repeat (req.rready_latency) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
   // Response phase
   vif_mstr_mp.drv_mstr_cb.rready <= 1'b1;
   vif_mstr_mp.drv_mstr_cb.req    <= 1'b0;
   repeat (req.rready_hold) begin
      if (vif_mstr_mp.drv_mstr_cb.rvalid !== 1'b1) begin
         break;
      end
      @(vif_mstr_mp.drv_mstr_cb);
   end
   while (vif_mstr_mp.drv_mstr_cb.rvalid === 1'b1) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
   // Tail
   vif_mstr_mp.drv_mstr_cb.rready <= 1'b0;
   drv_mstr_idle();
   repeat (req.tail_length) begin
      @(vif_mstr_mp.drv_mstr_cb);
   end
   
endtask : drv_mstr_write_req


task uvma_obi_drv_c::drv_slv_req(ref uvma_obi_slv_seq_item_c req);
   
   case (req.access_type)
      UVMA_OBI_ACCESS_READ: begin
         drv_slv_read_req(req);
      end
      
      UVMA_OBI_ACCESS_WRITE: begin
         drv_slv_write_req(req);
      end
      
      default: `uvm_fatal("OBI_DRV", $sformatf("Invalid access_type: %0d", req.access_type))
   endcase
   
endtask : drv_slv_req


task uvma_obi_drv_c::drv_slv_read_req(ref uvma_obi_slv_seq_item_c req);
   
   // Latency cycles
   repeat (req.gnt_latency) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
   // Address phase
   vif_slv_mp.drv_slv_cb.gnt <= 1'b1;
   repeat (req.access_latency) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
   // Response phase
   vif_slv_mp.drv_slv_cb.rvalid <= 1'b1;
   vif_slv_mp.drv_slv_cb.err <= req.err;
   for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
      vif_slv_mp.drv_slv_cb.rdata[ii] <= req.rdata[ii];
   end
   for (int unsigned ii=0; ii<cfg.ruser_width; ii++) begin
      vif_slv_mp.drv_slv_cb.ruser[ii] <= req.ruser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      vif_slv_mp.drv_slv_cb.rid[ii] <= req.rid[ii];
   end
   while (vif_slv_mp.drv_slv_cb.rready !== 1'b1) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
   // Hold cycles
   repeat (req.hold_duration) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
   // Idle
   vif_slv_mp.drv_slv_cb.gnt    <= 1'b0;
   vif_slv_mp.drv_slv_cb.rvalid <= 1'b0;
   drv_slv_idle();
   repeat (req.tail_length) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
endtask : drv_slv_read_req


task uvma_obi_drv_c::drv_slv_write_req(ref uvma_obi_slv_seq_item_c req);
   
   // Latency cycles
   repeat (req.gnt_latency) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
   // Address phase
   vif_slv_mp.drv_slv_cb.gnt <= 1'b1;
   repeat (req.access_latency) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
   // Response phase
   vif_slv_mp.drv_slv_cb.rvalid <= 1'b1;
   vif_slv_mp.drv_slv_cb.err <= req.err;
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      vif_slv_mp.drv_slv_cb.rid[ii] <= req.rid[ii];
   end
   while (vif_slv_mp.drv_slv_cb.rready !== 1'b1) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
   // Hold cycles
   repeat (req.hold_duration) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
   // Idle
   vif_slv_mp.drv_slv_cb.gnt    <= 1'b0;
   vif_slv_mp.drv_slv_cb.rvalid <= 1'b0;
   drv_slv_idle();
   repeat (req.tail_length) begin
      @(vif_slv_mp.drv_slv_cb);
   end
   
endtask : drv_slv_write_req


task uvma_obi_drv_c::wait_for_rsp(output uvma_obi_mon_trn_c rsp);
   
   mon_trn_fifo.get(rsp);
   
endtask : wait_for_rsp


task uvma_obi_drv_c::process_mstr_rsp(ref uvma_obi_mstr_seq_item_c req, ref uvma_obi_mon_trn_c rsp);
   
   req.rdata       = rsp.data;
   req.__has_error = rsp.err ;
   
endtask : process_mstr_rsp


task uvma_obi_drv_c::process_slv_rsp(ref uvma_obi_slv_seq_item_c rsp, ref uvma_obi_mon_trn_c req);
   
   rsp.orig_trn = req;
   
endtask : process_slv_rsp


task uvma_obi_drv_c::drv_mstr_idle();
   
   vif_mstr_mp.drv_mstr_cb.req    <= '0;
   vif_mstr_mp.drv_mstr_cb.rready <= '0;
   
   case (cfg.drv_idle)
      UVMA_OBI_DRV_IDLE_SAME: ;// Do nothing;
      
      UVMA_OBI_DRV_IDLE_ZEROS: begin
         vif_mstr_mp.drv_mstr_cb.addr  <= '0;
         vif_mstr_mp.drv_mstr_cb.we    <= '0;
         vif_mstr_mp.drv_mstr_cb.be    <= '0;
         vif_mstr_mp.drv_mstr_cb.wdata <= '0;
         vif_mstr_mp.drv_mstr_cb.auser <= '0;
         vif_mstr_mp.drv_mstr_cb.wuser <= '0;
         vif_mstr_mp.drv_mstr_cb.aid   <= '0;
      end
      
      UVMA_OBI_DRV_IDLE_RANDOM: begin
         vif_mstr_mp.drv_mstr_cb.addr  <= $urandom();
         vif_mstr_mp.drv_mstr_cb.we    <= $urandom();
         vif_mstr_mp.drv_mstr_cb.be    <= $urandom();
         vif_mstr_mp.drv_mstr_cb.wdata <= $urandom();
         vif_mstr_mp.drv_mstr_cb.auser <= $urandom();
         vif_mstr_mp.drv_mstr_cb.wuser <= $urandom();
         vif_mstr_mp.drv_mstr_cb.aid   <= $urandom();
      end
      
      UVMA_OBI_DRV_IDLE_X: begin
         vif_mstr_mp.drv_mstr_cb.addr  <= 'X;
         vif_mstr_mp.drv_mstr_cb.we    <= 'X;
         vif_mstr_mp.drv_mstr_cb.be    <= 'X;
         vif_mstr_mp.drv_mstr_cb.wdata <= 'X;
         vif_mstr_mp.drv_mstr_cb.auser <= 'X;
         vif_mstr_mp.drv_mstr_cb.wuser <= 'X;
         vif_mstr_mp.drv_mstr_cb.aid   <= 'X;
      end
      
      UVMA_OBI_DRV_IDLE_Z: begin
         vif_mstr_mp.drv_mstr_cb.addr  <= 'Z;
         vif_mstr_mp.drv_mstr_cb.we    <= 'Z;
         vif_mstr_mp.drv_mstr_cb.be    <= 'Z;
         vif_mstr_mp.drv_mstr_cb.wdata <= 'Z;
         vif_mstr_mp.drv_mstr_cb.auser <= 'Z;
         vif_mstr_mp.drv_mstr_cb.wuser <= 'Z;
         vif_mstr_mp.drv_mstr_cb.aid   <= 'Z;
      end
      
      default: `uvm_fatal("OBI_DRV", $sformatf("Invalid drv_idle: %0d", cfg.drv_idle))
   endcase
   
endtask : drv_mstr_idle


task uvma_obi_drv_c::drv_slv_idle();
   
   case (cfg.drv_idle)
      UVMA_OBI_DRV_IDLE_SAME: ;// Do nothing;
      
      UVMA_OBI_DRV_IDLE_ZEROS: begin
         vif_slv_mp.drv_slv_cb.rdata <= '0;
         vif_slv_mp.drv_slv_cb.err   <= '0;
         vif_slv_mp.drv_slv_cb.ruser <= '0;
         vif_slv_mp.drv_slv_cb.rid   <= '0;
      end
      
      UVMA_OBI_DRV_IDLE_RANDOM: begin
         vif_slv_mp.drv_slv_cb.rdata <= $urandom();
         vif_slv_mp.drv_slv_cb.err   <= $urandom();
         vif_slv_mp.drv_slv_cb.ruser <= $urandom();
         vif_slv_mp.drv_slv_cb.rid   <= $urandom();
      end
      
      UVMA_OBI_DRV_IDLE_X: begin
         vif_slv_mp.drv_slv_cb.rdata <= 'X;
         vif_slv_mp.drv_slv_cb.err   <= 'X;
         vif_slv_mp.drv_slv_cb.ruser <= 'X;
         vif_slv_mp.drv_slv_cb.rid   <= 'X;
      end
      
      UVMA_OBI_DRV_IDLE_Z: begin
         vif_slv_mp.drv_slv_cb.rdata <= 'Z;
         vif_slv_mp.drv_slv_cb.err   <= 'Z;
         vif_slv_mp.drv_slv_cb.ruser <= 'Z;
         vif_slv_mp.drv_slv_cb.rid   <= 'Z;
      end
      
      default: `uvm_fatal("OBI_DRV", $sformatf("Invalid drv_idle: %0d", cfg.drv_idle))
   endcase
   
endtask : drv_slv_idle


`endif // __UVMA_OBI_DRV_SV__
