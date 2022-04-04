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


`ifndef __UVMA_OBI_MEMORY_SLV_BASE_SEQ_SV__
`define __UVMA_OBI_MEMORY_SLV_BASE_SEQ_SV__


/**
 * TODO Describe uvma_obi_memory_slv_base_seq_c
 */
class uvma_obi_memory_slv_base_seq_c extends uvma_obi_memory_base_seq_c;

   // Fields


   `uvm_object_utils_begin(uvma_obi_memory_slv_base_seq_c)

   `uvm_object_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_slv_base_seq");

   /**
    * TODO Describe uvma_obi_memory_slv_base_seq_c::body()
    */
   extern task body();

   /**
    * TODO Describe uvma_obi_memory_slv_base_seq_c::do_response()
    */
   extern virtual task do_response(ref uvma_obi_memory_mon_trn_c mon_req);

   /**
    * Convenience function to encapsulate the add_* reponse functions to generate all non-data response fields
    */
   extern virtual function void add_r_fields(uvma_obi_memory_mon_trn_c mon_req, uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random ralid latency
    */
   extern virtual function void add_latencies(uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random error response as based on cfg knobs
    */
   extern virtual function void add_err(uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random exclusive okay response as based on cfg knobs
    */
   extern virtual function void add_exokay(uvma_obi_memory_mon_trn_c mon_req, uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random or custom ruser, default implementation writes 0
    */
   extern virtual function void add_rchk(uvma_obi_memory_slv_seq_item_c slv_rsp);

   /**
    * Standard method to add a random or custom rchk, default implementation writes 0
    */
   extern virtual function void add_ruser(uvma_obi_memory_slv_seq_item_c slv_rsp);

endclass : uvma_obi_memory_slv_base_seq_c


function uvma_obi_memory_slv_base_seq_c::new(string name="uvma_obi_memory_slv_base_seq");

   super.new(name);

endfunction : new


task uvma_obi_memory_slv_base_seq_c::body();

   uvma_obi_memory_mon_trn_c  mon_trn;

   forever begin
      // Wait for the monitor to send us the mstr's "req" with an access request
      p_sequencer.mon_trn_fifo.get(mon_trn);
      `uvm_info("OBI_MEMORY_SLV_SEQ", $sformatf("Got mon_trn:\n%s", mon_trn.sprint()), UVM_HIGH)
      do_response(mon_trn);
   end

endtask : body

task uvma_obi_memory_slv_base_seq_c::do_response(ref uvma_obi_memory_mon_trn_c mon_req);

   `uvm_fatal("OBI_MEMORY_SLV_SEQ", "Call to pure virtual task")

endtask : do_response

function void uvma_obi_memory_slv_base_seq_c::add_latencies(uvma_obi_memory_slv_seq_item_c slv_rsp);

   slv_rsp.rvalid_latency = cfg.calc_random_rvalid_latency();

endfunction : add_latencies

function void uvma_obi_memory_slv_base_seq_c::add_r_fields(uvma_obi_memory_mon_trn_c mon_req, uvma_obi_memory_slv_seq_item_c slv_rsp);

   // This is just a convenience function
   // Take care to leave rchk last as it will likely incorporate a checksum of all other response fields

   slv_rsp.rid = mon_req.aid;
   add_latencies(slv_rsp);
   if (cfg.version >= UVMA_OBI_MEMORY_VERSION_1P2) begin
      add_err(slv_rsp);
      add_exokay(mon_req, slv_rsp);
      add_ruser(slv_rsp);
      add_rchk(slv_rsp);
   end

endfunction : add_r_fields

function void uvma_obi_memory_slv_base_seq_c::add_err(uvma_obi_memory_slv_seq_item_c slv_rsp);

   slv_rsp.err = cfg.calc_random_err(slv_rsp.orig_trn.address);

endfunction : add_err

function void uvma_obi_memory_slv_base_seq_c::add_exokay(uvma_obi_memory_mon_trn_c mon_req, uvma_obi_memory_slv_seq_item_c slv_rsp);

   // Only respond exokay == 1 to SC or LR as signaled by atop
   if (mon_req.atop[5] != 1'b1 || !(mon_req.atop[4:0] inside {5'h2, 5'h3})) begin
      slv_rsp.exokay = 0;
      return;
   end

   slv_rsp.exokay = cfg.calc_random_exokay(slv_rsp.orig_trn.address);

endfunction : add_exokay


function void uvma_obi_memory_slv_base_seq_c::add_ruser(uvma_obi_memory_slv_seq_item_c slv_rsp);

   slv_rsp.ruser = '0;

endfunction : add_ruser

function void uvma_obi_memory_slv_base_seq_c::add_rchk(uvma_obi_memory_slv_seq_item_c slv_rsp);

   // FIXME:need to implement this
   // slv_rsp.rchk = '0;

endfunction : add_rchk


`endif // __UVMA_OBI_MEMORY_SLV_BASE_SEQ_SV__
