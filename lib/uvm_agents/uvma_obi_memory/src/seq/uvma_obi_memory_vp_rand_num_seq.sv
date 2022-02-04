//
// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
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

`ifndef __UVMA_OBI_MEMORY_VP_RAND_NUM_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_RAND_NUM_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvma_obi_memory_vp_rand_num_seq_c extends uvma_obi_memory_vp_base_seq_c;

   rand uvma_obi_memory_data_b_t   rdata;

   `uvm_object_utils_begin(uvma_obi_memory_vp_rand_num_seq_c)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_rand_num_seq_c");

   /**
    * Implement number of peripherals
    */
   extern virtual function int unsigned get_num_words();

   /**
    * Implement sequence that will return a random number
    */
   extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

endclass : uvma_obi_memory_vp_rand_num_seq_c


function uvma_obi_memory_vp_rand_num_seq_c::new(string name="uvma_obi_memory_vp_rand_num_seq_c");

   super.new(name);

endfunction : new

function int unsigned uvma_obi_memory_vp_rand_num_seq_c::get_num_words();

   return 1;

endfunction : get_num_words

task uvma_obi_memory_vp_rand_num_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;

   `uvm_create(slv_rsp)

   slv_rsp.orig_trn = mon_trn;
   if (!this.randomize()) begin
      `uvm_fatal("VPRNDSEQ", "Failed to randomize")
   end
   else begin
      slv_rsp.rdata = this.rdata;
   end
   slv_rsp.err = 1'b0;

   `uvm_info("VPRNDSEQ", $sformatf("Issuing a random number: 0x%08x", slv_rsp.rdata), UVM_HIGH);

   add_r_fields(mon_trn, slv_rsp);
   `uvm_send(slv_rsp)

endtask : vp_body

`endif // __UVMA_OBI_MEMORY_VP_RAND_NUM_SEQ_SV__
