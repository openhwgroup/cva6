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


`ifndef __UVMA_OBI_MEMORY_DRV_SV__
`define __UVMA_OBI_MEMORY_DRV_SV__


/**
 * Component driving a Open Bus Interface virtual interface (uvma_obi_if).
 * @note The req & rsp's roles are switched when this driver is in 'slv' mode.
 * @todo Move implementation to a sequence-based approach
 */
class uvma_obi_memory_drv_c extends uvm_driver#(
   .REQ(uvma_obi_memory_base_seq_item_c),
   .RSP(uvma_obi_memory_mon_trn_c      )
);

   // Objects
   uvma_obi_memory_cfg_c    cfg;
   uvma_obi_memory_cntxt_c  cntxt;

   // TLM
   uvm_analysis_port     #(uvma_obi_memory_mstr_seq_item_c)  mstr_ap;
   uvm_analysis_port     #(uvma_obi_memory_slv_seq_item_c )  slv_ap ;
   uvm_tlm_analysis_fifo #(uvma_obi_memory_mon_trn_c      )  mon_trn_fifo;

   // Handles to virtual interface modports
   virtual uvma_obi_memory_if.active_mstr_mp  mstr_mp;
   virtual uvma_obi_memory_if.active_slv_mp   slv_mp ;

   `uvm_component_utils_begin(uvma_obi_memory_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_drv", uvm_component parent=null);

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
   extern task drv_pre_reset();

   /**
    * Called by run_phase() while agent is in reset state.
    */
   extern task drv_in_reset();

   /**
    * Called by run_phase() while agent is in post-reset state.
    */
   extern task drv_post_reset();

   /**
    * Drives the 'gnt' signal in response to 'req' being asserted.
    */
   extern task drv_slv_gnt();

   /**
    * TODO Describe uvma_obi_drv::prep_req()
    */
   extern task prep_req(ref uvma_obi_memory_base_seq_item_c req);

   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    * This task handles both READ and WRITE transactions.
    */
   extern task drv_mstr_req(ref uvma_obi_memory_mstr_seq_item_c req);

   /**
    * Drives the virtual interface's (cntxt.vif) signals using req's contents.
    */
   extern task drv_slv_req(ref uvma_obi_memory_slv_seq_item_c req);

   /**
    * Drives the interface's signals using req's contents.
    */
   extern virtual task drv_slv_read_req(ref uvma_obi_memory_slv_seq_item_c req);

   /**
    * Drives the interface's signals using req's contents.
    */
   extern virtual task drv_slv_write_req(ref uvma_obi_memory_slv_seq_item_c req);

   /**
    * TODO Describe uvma_obi_memory_drv_c::wait_for_rsp()
    */
   extern task wait_for_rsp(output uvma_obi_memory_mon_trn_c rsp);

   /**
    * TODO Describe uvma_obi_memory_drv_c::process_mstr_rsp()
    */
   extern task process_mstr_rsp(ref uvma_obi_memory_mstr_seq_item_c req, ref uvma_obi_memory_mon_trn_c rsp);

   /**
    * TODO Describe uvma_obi_memory_drv_c::process_slv_rsp()
    */
   extern task process_slv_rsp(ref uvma_obi_memory_slv_seq_item_c rsp, ref uvma_obi_memory_mon_trn_c req);

   /**
    * TODO Describe uvma_obi_memory_drv_c::drv_mstr_idle()
    */
   extern task drv_mstr_idle();

   /**
    * Drive an idle response state onto the OBI (including rvalid == 0)
    */
   extern task drv_slv_idle();

endclass : uvma_obi_memory_drv_c


function uvma_obi_memory_drv_c::new(string name="uvma_obi_memory_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_obi_memory_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_obi_memory_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_obi_memory_cfg_c)::set(this, "*", "cfg", cfg);

   void'(uvm_config_db#(uvma_obi_memory_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_obi_memory_cntxt_c)::set(this, "*", "cntxt", cntxt);
   mstr_mp = cntxt.vif.active_mstr_mp;
   slv_mp  = cntxt.vif.active_slv_mp ;

   mstr_ap      = new("mstr_ap"     , this);
   slv_ap       = new("slv_ap"      , this);
   mon_trn_fifo = new("mon_trn_fifo", this);

endfunction : build_phase


task uvma_obi_memory_drv_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   if (cfg.enabled && cfg.is_active) begin
      fork
         begin : chan_a
            forever begin
               drv_slv_gnt();
            end
         end

         begin : chan_r
            forever begin
               case (cntxt.reset_state)
                  UVMA_OBI_MEMORY_RESET_STATE_PRE_RESET : drv_pre_reset ();
                  UVMA_OBI_MEMORY_RESET_STATE_IN_RESET  : drv_in_reset  ();
                  UVMA_OBI_MEMORY_RESET_STATE_POST_RESET: drv_post_reset();

                  default: `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Invalid reset_state: %0d", cntxt.reset_state))
               endcase
            end
         end
      join_none
   end

endtask : run_phase


task uvma_obi_memory_drv_c::drv_pre_reset();

   slv_mp.drv_slv_cb.gnt    <= 1'b0;
   slv_mp.drv_slv_cb.rvalid <= 1'b0;
   if (cfg.is_1p2_or_higher()) begin
      slv_mp.drv_slv_cb.gntpar    <= 1'b1;
      slv_mp.drv_slv_cb.rvalidpar <= 1'b1;
   end

   case (cfg.drv_mode)
      UVMA_OBI_MEMORY_MODE_MSTR: @(mstr_mp.drv_mstr_cb);
      UVMA_OBI_MEMORY_MODE_SLV : @(slv_mp .drv_slv_cb );

      default: `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Invalid drv_mode: %0d", cfg.drv_mode))
   endcase

endtask : drv_pre_reset


task uvma_obi_memory_drv_c::drv_in_reset();

   case (cfg.drv_mode)
      UVMA_OBI_MEMORY_MODE_MSTR: begin
         @(mstr_mp.drv_mstr_cb);
         drv_mstr_idle();
      end

      UVMA_OBI_MEMORY_MODE_SLV : begin
         slv_mp.drv_slv_cb.rdata <= '0;
         @(slv_mp.drv_slv_cb);
         slv_mp.drv_slv_cb.rdata <= '0;
         drv_slv_idle();
      end

      default: `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Invalid drv_mode: %0d", cfg.drv_mode))
   endcase

endtask : drv_in_reset


task uvma_obi_memory_drv_c::drv_post_reset();

   uvma_obi_memory_mstr_seq_item_c  mstr_req;
   uvma_obi_memory_slv_seq_item_c   slv_req;
   uvma_obi_memory_mon_trn_c        mstr_rsp;
   uvma_obi_memory_mon_trn_c        slv_rsp;

   case (cfg.drv_mode)
      UVMA_OBI_MEMORY_MODE_MSTR: begin
         // 1. Get next req from sequence and drive it on the vif
         seq_item_port.get_next_item(req);
         prep_req(req);
         if (!$cast(mstr_req, req)) begin
            `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Could not cast 'req' (%s) to 'mstr_req' (%s)", $typename(req), $typename(mstr_req)))
         end
         `uvm_info("OBI_MEMORY_DRV", $sformatf("Got mstr_req:\n%s", mstr_req.sprint()), UVM_HIGH)
         drv_mstr_req(mstr_req);

         // 2. Wait for the monitor to send us the slv's rsp with the results of the req
         wait_for_rsp(slv_rsp);
         process_mstr_rsp(mstr_req, slv_rsp);

         // 3. Send out to TLM and tell sequencer we're ready for the next sequence item
         mstr_ap.write(mstr_req);
         seq_item_port.item_done();
      end

      UVMA_OBI_MEMORY_MODE_SLV: begin
         seq_item_port.try_next_item(req);
         if (req != null) begin
            // 1. Get next req from sequence to reply to mstr and drive it on the vif
            prep_req(req);
            if (!$cast(slv_req, req)) begin
               `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Could not cast 'req' (%s) to 'slv_req' (%s)", $typename(req), $typename(slv_req)))
            end
            `uvm_info("OBI_MEMORY_DRV", $sformatf("Got slv_req:\n%s", slv_req.sprint()), UVM_HIGH)
            drv_slv_req(slv_req);

            // 2. Send out to TLM and tell sequencer we're ready for the next sequence item
            slv_ap.write(slv_req);
            seq_item_port.item_done();
         end
         else begin
            drv_slv_idle();
            @(slv_mp.drv_slv_cb);
         end
      end

      default: `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Invalid drv_mode: %0d", cfg.drv_mode))
   endcase

endtask : drv_post_reset


task uvma_obi_memory_drv_c::drv_slv_gnt();

   case (cntxt.reset_state)
      UVMA_OBI_MEMORY_RESET_STATE_POST_RESET: begin

         // Pre-calculate the "next" latency
         int unsigned effective_latency = cfg.calc_random_gnt_latency();

         // In case 0 latency was selected, we must go ahead and drive gnt (combinatorial path)
         if (effective_latency == 0) begin
            slv_mp.drv_slv_cb.gnt <= 1'b1; 
            if (cfg.is_1p2_or_higher()) begin
               slv_mp.drv_slv_cb.gntpar <= 1'b0;
            end
         end
         else begin
            slv_mp.drv_slv_cb.gnt <= 1'b0;
            if (cfg.is_1p2_or_higher()) begin
               slv_mp.drv_slv_cb.gntpar <= 1'b1;
            end
         end

         // Advance the clock
         @(slv_mp.drv_slv_cb);

         // Break out of this loop upon the next req and gnt
         while (!(slv_mp.drv_slv_cb.req && slv_mp.drv_slv_cb.gnt)) begin
            // Only count down a non-zero effective latency if someone is requesting (req asserted)
            if (effective_latency && slv_mp.drv_slv_cb.req)
               effective_latency--;

            if (!effective_latency) begin
               slv_mp.drv_slv_cb.gnt <= 1'b1;
               if (cfg.is_1p2_or_higher()) begin
                  slv_mp.drv_slv_cb.gntpar <= 1'b0;
               end
            end

            @(slv_mp.drv_slv_cb);
         end
      end
      // If we are in another reset state, it is critical to advance time within the reset loop
      default: @(slv_mp.drv_slv_cb);
   endcase

endtask : drv_slv_gnt

task uvma_obi_memory_drv_c::prep_req(ref uvma_obi_memory_base_seq_item_c req);

   `uvml_hrtbt()
   req.cfg = cfg;

endtask : prep_req

// Both Master READ and WRITE transactions are handled here because the signalling is almost identical.
// TODO: this task is yet to be fully tested as the CV32E4 cores are always the OBI bus master.
task uvma_obi_memory_drv_c::drv_mstr_req(ref uvma_obi_memory_mstr_seq_item_c req);

   if (req.access_type != UVMA_OBI_MEMORY_ACCESS_READ && req.access_type != UVMA_OBI_MEMORY_ACCESS_WRITE) begin
     `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Invalid access_type: %0d", req.access_type))
   end

   // Req Latency cycles
   repeat (req.req_latency) begin
      @(mstr_mp.drv_mstr_cb);
   end

   // Address phase
   mstr_mp.drv_mstr_cb.req <= 1'b1;
   mstr_mp.drv_mstr_cb.we  <= req.access_type;
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      mstr_mp.drv_mstr_cb.addr[ii] <= req.address[ii];
   end
   for (int unsigned ii=0; ii<(cfg.data_width/8); ii++) begin
      mstr_mp.drv_mstr_cb.be[ii] <= req.be[ii];
   end
   for (int unsigned ii=0; ii<cfg.auser_width; ii++) begin
      mstr_mp.drv_mstr_cb.auser[ii] <= req.auser[ii];
   end
   for (int unsigned ii=0; ii<cfg.id_width; ii++) begin
      mstr_mp.drv_mstr_cb.aid[ii] <= req.id[ii];
   end

   // Handle WRITE
   if (req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
       for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
          mstr_mp.drv_mstr_cb.wdata[ii] <= req.wdata[ii];
       end
       for (int unsigned ii=0; ii<cfg.wuser_width; ii++) begin
          mstr_mp.drv_mstr_cb.wuser[ii] <= req.wuser[ii];
       end
   end

   // Wait for grant
   while (mstr_mp.drv_mstr_cb.gnt !== 1'b1) begin
      @(mstr_mp.drv_mstr_cb);
   end

   // Wait for rvalid
   if (mstr_mp.drv_mstr_cb.rvalid !== 1'b1) begin
      while (mstr_mp.drv_mstr_cb.rvalid !== 1'b1) begin
         @(mstr_mp.drv_mstr_cb);
      end
   end
   repeat (req.rready_latency) begin
      @(mstr_mp.drv_mstr_cb);
   end

   // Response phase
   mstr_mp.drv_mstr_cb.rready <= 1'b1;
   mstr_mp.drv_mstr_cb.req    <= 1'b0;
   repeat (req.rready_hold) begin
      if (mstr_mp.drv_mstr_cb.rvalid !== 1'b1) begin
         break;
      end
      @(mstr_mp.drv_mstr_cb);
   end
   while (mstr_mp.drv_mstr_cb.rvalid === 1'b1) begin
      @(mstr_mp.drv_mstr_cb);
   end

   // Tail
   mstr_mp.drv_mstr_cb.rready <= 1'b0;
   drv_mstr_idle();
   repeat (req.tail_length) begin
      @(mstr_mp.drv_mstr_cb);
   end

endtask : drv_mstr_req


task uvma_obi_memory_drv_c::drv_slv_req(ref uvma_obi_memory_slv_seq_item_c req);

   case (req.access_type)
      UVMA_OBI_MEMORY_ACCESS_READ: begin
         drv_slv_read_req(req);
      end

      UVMA_OBI_MEMORY_ACCESS_WRITE: begin
         drv_slv_write_req(req);
      end

      default: `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Invalid access_type: %0d", req.access_type))
   endcase

endtask : drv_slv_req


task uvma_obi_memory_drv_c::drv_slv_read_req(ref uvma_obi_memory_slv_seq_item_c req);

   `uvm_info("OBI_MEMORY_DRV", $sformatf("drv_slv_read_req: %8h", req.rdata), UVM_HIGH)
   `uvm_info("OBI_MEMORY_DRV", $sformatf("drv latency: %0d", req.rvalid_latency), UVM_HIGH)
   repeat (req.rvalid_latency) begin
      @(slv_mp.drv_slv_cb);
   end
   slv_mp.drv_slv_cb.rvalid <= 1'b1;
   if (cfg.is_1p2_or_higher()) begin
      slv_mp.drv_slv_cb.rvalidpar <= 1'b0;
      slv_mp.drv_slv_cb.rid       <= req.rid;
      slv_mp.drv_slv_cb.err       <= req.err;
      slv_mp.drv_slv_cb.exokay    <= req.exokay;
   end
   for (int unsigned ii=0; ii<cfg.data_width; ii++) begin
      slv_mp.drv_slv_cb.rdata[ii] <= req.rdata[ii];
   end
   @(slv_mp.drv_slv_cb);
   `uvm_info("OBI_MEMORY_DRV", "drv_slv_read_req FIN", UVM_HIGH)
   drv_slv_idle();

endtask : drv_slv_read_req


task uvma_obi_memory_drv_c::drv_slv_write_req(ref uvma_obi_memory_slv_seq_item_c req);

   `uvm_info("OBI_MEMORY_DRV", $sformatf("drv_slv_write_req: %8h", req.rdata), UVM_HIGH)
   `uvm_info("OBI_MEMORY_DRV", $sformatf("drv latency: %0d", req.rvalid_latency), UVM_HIGH)
   repeat (req.rvalid_latency) begin
      @(slv_mp.drv_slv_cb);
   end
   slv_mp.drv_slv_cb.rvalid <= 1'b1;
   if (cfg.is_1p2_or_higher()) begin
      slv_mp.drv_slv_cb.rvalidpar <= 1'b0;
      slv_mp.drv_slv_cb.rid       <= req.rid;
      slv_mp.drv_slv_cb.err       <= req.err;
      slv_mp.drv_slv_cb.exokay    <= req.exokay;
   end
   @(slv_mp.drv_slv_cb);
   `uvm_info("OBI_MEMORY_DRV", "drv_slv_write_req FIN", UVM_HIGH)
   drv_slv_idle();

endtask : drv_slv_write_req


task uvma_obi_memory_drv_c::wait_for_rsp(output uvma_obi_memory_mon_trn_c rsp);

   mon_trn_fifo.get(rsp);

endtask : wait_for_rsp


task uvma_obi_memory_drv_c::process_mstr_rsp(ref uvma_obi_memory_mstr_seq_item_c req, ref uvma_obi_memory_mon_trn_c rsp);

   req.rdata       = rsp.data;
   req.__has_error = rsp.err ;

endtask : process_mstr_rsp


task uvma_obi_memory_drv_c::process_slv_rsp(ref uvma_obi_memory_slv_seq_item_c rsp, ref uvma_obi_memory_mon_trn_c req);

   rsp.orig_trn = req;

endtask : process_slv_rsp


task uvma_obi_memory_drv_c::drv_mstr_idle();

   mstr_mp.drv_mstr_cb.req    <= '0;
   mstr_mp.drv_mstr_cb.rready <= '0;

   case (cfg.drv_idle)
      UVMA_OBI_MEMORY_DRV_IDLE_SAME: ;// Do nothing;

      UVMA_OBI_MEMORY_DRV_IDLE_ZEROS: begin
         mstr_mp.drv_mstr_cb.addr  <= '0;
         mstr_mp.drv_mstr_cb.we    <= '0;
         mstr_mp.drv_mstr_cb.be    <= '0;
         mstr_mp.drv_mstr_cb.wdata <= '0;
         mstr_mp.drv_mstr_cb.auser <= '0;
         mstr_mp.drv_mstr_cb.wuser <= '0;
         mstr_mp.drv_mstr_cb.aid   <= '0;
      end

      UVMA_OBI_MEMORY_DRV_IDLE_RANDOM: begin
         // SVTB.29.1.3.1 - Banned random number system functions and methods calls
         // Waive-abe because cfg.drv_idle is constrainable.
         //@DVT_LINTER_WAIVER_START "MT20211214_5" disable SVTB.29.1.3.1
         mstr_mp.drv_mstr_cb.addr  <= $urandom();
         mstr_mp.drv_mstr_cb.we    <= $urandom();
         mstr_mp.drv_mstr_cb.be    <= $urandom();
         mstr_mp.drv_mstr_cb.wdata <= $urandom();
         mstr_mp.drv_mstr_cb.auser <= $urandom();
         mstr_mp.drv_mstr_cb.wuser <= $urandom();
         mstr_mp.drv_mstr_cb.aid   <= $urandom();
         //@DVT_LINTER_WAIVER_END "MT20211214_5"
      end

      UVMA_OBI_MEMORY_DRV_IDLE_X: begin
         mstr_mp.drv_mstr_cb.addr  <= 'X;
         mstr_mp.drv_mstr_cb.we    <= 'X;
         mstr_mp.drv_mstr_cb.be    <= 'X;
         mstr_mp.drv_mstr_cb.wdata <= 'X;
         mstr_mp.drv_mstr_cb.auser <= 'X;
         mstr_mp.drv_mstr_cb.wuser <= 'X;
         mstr_mp.drv_mstr_cb.aid   <= 'X;
      end

      UVMA_OBI_MEMORY_DRV_IDLE_Z: begin
         mstr_mp.drv_mstr_cb.addr  <= 'Z;
         mstr_mp.drv_mstr_cb.we    <= 'Z;
         mstr_mp.drv_mstr_cb.be    <= 'Z;
         mstr_mp.drv_mstr_cb.wdata <= 'Z;
         mstr_mp.drv_mstr_cb.auser <= 'Z;
         mstr_mp.drv_mstr_cb.wuser <= 'Z;
         mstr_mp.drv_mstr_cb.aid   <= 'Z;
      end

      default: `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Invalid drv_idle: %0d", cfg.drv_idle))
   endcase

endtask : drv_mstr_idle


task uvma_obi_memory_drv_c::drv_slv_idle();

   slv_mp.drv_slv_cb.rvalid <= '0;
   if (cfg.is_1p2_or_higher()) begin
      slv_mp.drv_slv_cb.rvalidpar <= 1'b1;
   end

   case (cfg.drv_idle)

      UVMA_OBI_MEMORY_DRV_IDLE_SAME: ;// Do nothing;

      UVMA_OBI_MEMORY_DRV_IDLE_ZEROS: begin
         //`uvm_info("OBI_MEMORY_DRV", $sformatf("Invalid drv_zeros: %0d", cfg.drv_idle), UVM_NONE)
         slv_mp.drv_slv_cb.rdata <= '0;
         slv_mp.drv_slv_cb.err   <= '0;
         slv_mp.drv_slv_cb.ruser <= '0;
         slv_mp.drv_slv_cb.rid   <= '0;
      end

      UVMA_OBI_MEMORY_DRV_IDLE_RANDOM: begin
         `uvm_info("OBI_MEMORY_DRV", $sformatf("Invalid drv_random: %0d", cfg.drv_idle), UVM_NONE)
         // SVTB.29.1.3.1 - Banned random number system functions and methods calls
         // Waive-abe because cfg.drv_idle is constrainable.
         //@DVT_LINTER_WAIVER_START "MT20211214_6" disable SVTB.29.1.3.1
         slv_mp.drv_slv_cb.rdata <= $urandom();
         slv_mp.drv_slv_cb.err   <= $urandom();
         slv_mp.drv_slv_cb.ruser <= $urandom();
         slv_mp.drv_slv_cb.rid   <= $urandom();
         //@DVT_LINTER_WAIVER_END "MT20211214_6"
      end

      UVMA_OBI_MEMORY_DRV_IDLE_X: begin
         `uvm_info("OBI_MEMORY_DRV", $sformatf("Invalid drv_idle: %0d", cfg.drv_idle), UVM_NONE)
         slv_mp.drv_slv_cb.rdata <= 'X;
         slv_mp.drv_slv_cb.err   <= 'X;
         slv_mp.drv_slv_cb.ruser <= 'X;
         slv_mp.drv_slv_cb.rid   <= 'X;
      end

      UVMA_OBI_MEMORY_DRV_IDLE_Z: begin
         `uvm_info("OBI_MEMORY_DRV", $sformatf("Invalid drv_Z: %0d", cfg.drv_idle), UVM_NONE)
         slv_mp.drv_slv_cb.rdata <= 'Z;
         slv_mp.drv_slv_cb.err   <= 'Z;
         slv_mp.drv_slv_cb.ruser <= 'Z;
         slv_mp.drv_slv_cb.rid   <= 'Z;
      end

      default: `uvm_fatal("OBI_MEMORY_DRV", $sformatf("Invalid drv_idle: %0d", cfg.drv_idle))
   endcase

endtask : drv_slv_idle


`endif // __UVMA_OBI_MEMORY_DRV_SV__
