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


`ifndef __UVMA_OBI_MEMORY_SLV_SEQ_SV__
`define __UVMA_OBI_MEMORY_SLV_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvma_obi_memory_slv_seq_c extends uvma_obi_memory_slv_base_seq_c;

   // Queue of virtual peripheral sequences to spawn when this sequence is spawned
   uvma_obi_memory_vp_base_seq_c vp_seq_q[$];

   // Lookup table to trigger sequences when bus address is detected
   uvma_obi_memory_vp_base_seq_c vp_seq_table[bit[31:0]];

   `uvm_object_utils_begin(uvma_obi_memory_slv_seq_c)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_slv_seq");

   /**
    * Register sequences with a range of addresses on this OBI
    * Waiving Verissimo SVTB.32.2.0: Pass strings by reference unless otherwise needed
    */
   extern virtual function uvma_obi_memory_vp_base_seq_c register_vp_vseq(string name,                  //@DVT_LINTER_WAIVER "MT20211228_9" disable SVTB.32.2.0
                                                                          bit[31:0] start_address,
                                                                          uvm_object_wrapper seq_type);

   /**
    * Main sequence body
    */
   extern virtual task body();

   /**
    * Spawn virtual peripheral sequences when this sequence starts
    */
   extern virtual task spawn_vp_sequences();

   /**
    * TODO Describe uvma_obi_memory_slv_seq_c::do_response()
    */
   extern virtual task do_response(ref uvma_obi_memory_mon_trn_c mon_req);

   /**
    * TODO Describe uvma_obi_memory_slv_seq_c::do_mem_operation()
    */
   extern virtual task do_mem_operation(ref uvma_obi_memory_mon_trn_c mon_req);

endclass : uvma_obi_memory_slv_seq_c


function uvma_obi_memory_slv_seq_c::new(string name="uvma_obi_memory_slv_seq");

   super.new(name);
   if (!this.randomize()) begin
      `uvm_fatal("OBIMEMSLVSEQ", "Randomize failed");
   end

endfunction : new

task uvma_obi_memory_slv_seq_c::body();

   uvma_obi_memory_mon_trn_c  mon_trn;

   // Start the virtual peripheral sequences
   spawn_vp_sequences();

   fork
      begin
         forever begin
            // Wait for the monitor to send us the mstr's "req" with an access request
            p_sequencer.mon_trn_fifo.get(mon_trn);
            `uvm_info("SLV_SEQ", $sformatf("Got mon_trn:\n%s", mon_trn.sprint()), UVM_DEBUG)
            do_response(mon_trn);
         end
      end

   join_none

endtask : body


task uvma_obi_memory_slv_seq_c::do_response(ref uvma_obi_memory_mon_trn_c mon_req);

   bit  err_req;
   bit  err_siz;

   `uvm_info("SLV_SEQ", $sformatf("mon_req.address before data_addr_dec remap: x%h", mon_req.address), UVM_HIGH/*NONE*/)

   // Check the virtual peripheral address hash table to see if transaction should be sent to a virtual peripheral
   if (vp_seq_table.exists(mon_req.address)) begin
      vp_seq_table[mon_req.address].mon_trn_q.push_back(mon_req);
      return;
   end

   // If we fell through, then handle the transaction locally
   `uvm_info("SLV_SEQ", $sformatf("VP not handled: x%h", mon_req.address), UVM_HIGH)
   err_req  = mon_req.err;
   if (err_req) `uvm_info("SLV_SEQ", $sformatf("ERROR1: mon_req.err=%0b", mon_req.err), UVM_HIGH/*NONE*/)
   err_siz = 0;
   if (err_siz) `uvm_info("SLV_SEQ", $sformatf("ERROR2: mon_req.address=%0h", mon_req.address), UVM_HIGH/*NONE*/)

   if (!(err_req | err_siz)) begin
      do_mem_operation(mon_req);
   end
   else begin
      uvma_obi_memory_slv_seq_item_c  slv_rsp;

      `uvm_create(slv_rsp)
      slv_rsp.orig_trn = mon_req;

      `uvm_info("SLV_SEQ", $sformatf("Error!\n%s", mon_req.sprint()), UVM_LOW)
      if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
         // TODO: need to figured out what a proper error response is
         slv_rsp.rdata = 32'hdead_beef;
      end
      add_r_fields(mon_req, slv_rsp);
      slv_rsp.set_sequencer(p_sequencer);
      `uvm_send(slv_rsp)
   end

endtask : do_response

task uvma_obi_memory_slv_seq_c::do_mem_operation(ref uvma_obi_memory_mon_trn_c mon_req);

   bit [31:0] word_aligned_addr;

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   `uvm_create(slv_rsp)
   slv_rsp.orig_trn = mon_req;
   slv_rsp.access_type = mon_req.access_type;

   word_aligned_addr = { mon_req.address[31:2], 2'h0 };

   `uvm_info("SLV_SEQ", $sformatf("Performing operation:\n%s", mon_req.sprint()), UVM_HIGH)
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      if (mon_req.be[3]) cntxt.mem.write(word_aligned_addr+3, mon_req.data[31:24]);
      if (mon_req.be[2]) cntxt.mem.write(word_aligned_addr+2, mon_req.data[23:16]);
      if (mon_req.be[1]) cntxt.mem.write(word_aligned_addr+1, mon_req.data[15:08]);
      if (mon_req.be[0]) cntxt.mem.write(word_aligned_addr+0, mon_req.data[07:00]);
   end
   else begin
      if (mon_req.be[3]) slv_rsp.rdata[31:24] = cntxt.mem.read(word_aligned_addr+3);
      if (mon_req.be[2]) slv_rsp.rdata[23:16] = cntxt.mem.read(word_aligned_addr+2);
      if (mon_req.be[1]) slv_rsp.rdata[15:08] = cntxt.mem.read(word_aligned_addr+1);
      if (mon_req.be[0]) slv_rsp.rdata[07:00] = cntxt.mem.read(word_aligned_addr+0);
   end

   add_r_fields(mon_req, slv_rsp);
   slv_rsp.set_sequencer(p_sequencer);
   `uvm_send(slv_rsp)

endtask : do_mem_operation

function uvma_obi_memory_vp_base_seq_c uvma_obi_memory_slv_seq_c::register_vp_vseq(string name,
                                                                                   bit[31:0] start_address,
                                                                                   uvm_object_wrapper seq_type);

   uvma_obi_memory_vp_base_seq_c vp_seq;

   // Create an instance of the sequence type passed in,
   // Ensure that the sequence type is derived from uvma_obi_memory_vp_base_seq_c
   if (!$cast(vp_seq, seq_type.create_object(name))) begin
      `uvm_fatal("OBIVPVSEQ", $sformatf("Could not cast seq_type of type name: %s to a uvma_obi_memory_vp_base_seq_c type", seq_type.get_type_name()))
   end

   // Sanity check num_words
   if (vp_seq.get_num_words() == 0) begin
      `uvm_fatal("OBIVPVSEQ", $sformatf("num_words for type %s cannot be zero", seq_type.get_type_name()))
   end

   // Configure fields in the virtual peripheral sequence
   vp_seq.start_address = start_address;

   // Use hash to efficiently look up word-aligned addresses to this handle
   for (int unsigned word = 0; word < vp_seq.get_num_words(); word++) begin
      bit[31:0] addr = (start_address & ~32'h3) + (4 * word);

      // If an address is being claimed twice, then issue a fatal error
      if (vp_seq_table.exists(addr)) begin
         `uvm_fatal("OBIVPVSEQ", $sformatf("address: 0x%08x, tried to register vp_vseq [%s], but vp_vseq [%s] already registered",
                                           addr, vp_seq.get_name(), vp_seq_table[addr].get_name()));
      end
      `uvm_info("OBIVPSEQ", $sformatf("Virtual register: %s, addr: 0x%08x", vp_seq.get_full_name(), addr), UVM_LOW);

      vp_seq_table[addr] = vp_seq;
   end
   vp_seq_q.push_back(vp_seq);

   return vp_seq;

endfunction : register_vp_vseq

task uvma_obi_memory_slv_seq_c::spawn_vp_sequences();

   if (p_sequencer == null) begin
      `uvm_fatal("SLV_SEQ", "Cannot find p_sequencer handle to spawn virtual sequences on");
   end

   // Iterate through the queue and spawn all unique register virtual peripheral sequence objects on this sequencer
   foreach (vp_seq_q[i]) begin
      automatic int ii = i;

      fork
         vp_seq_q[ii].start(p_sequencer, this);
      join_none
   end

endtask : spawn_vp_sequences

`endif // __UVMA_OBI_MEMORY_SLV_SEQ__
