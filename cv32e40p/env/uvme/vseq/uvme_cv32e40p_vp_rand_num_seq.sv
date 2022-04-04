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

`ifndef __UVME_CV32E40P_VP_RAND_NUM_SEQ_SV__
`define __UVME_CV32E40P_VP_RAND_NUM_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvme_cv32e40p_vp_rand_num_seq_c extends uvma_obi_memory_vp_base_seq_c;

   localparam NUM_WORDS = 1;

   uvme_cv32e40p_cntxt_c cv32e40p_cntxt;

   `uvm_object_utils_begin(uvme_cv32e40p_vp_rand_num_seq_c)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40p_vp_rand_num_seq_c");

   /**
    * Implement number of peripherals
    */
   extern virtual function int unsigned get_num_words();

   /**
    * Implement sequence that will return a random number
    */
   extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

endclass : uvme_cv32e40p_vp_rand_num_seq_c


function uvme_cv32e40p_vp_rand_num_seq_c::new(string name="uvme_cv32e40p_vp_rand_num_seq_c");

   super.new(name);

endfunction : new

function int unsigned uvme_cv32e40p_vp_rand_num_seq_c::get_num_words();

   return NUM_WORDS;

endfunction  : get_num_words

task uvme_cv32e40p_vp_rand_num_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;   

   `uvm_create(slv_rsp)

   slv_rsp.orig_trn = mon_trn;
   // SVTB.29.1.3.1 - Banned random number system functions and methods calls
   // Waived because it is very unlikely we'd ever need to control this value.
   slv_rsp.rdata = $urandom(); //@DVT_LINTER_WAIVER "MT20211214_10" disable SVTB.29.1.3.1
   slv_rsp.err = 1'b0;

   `uvm_info("VPRNDSEQ", $sformatf("Issuing a random number: 0x%08x", slv_rsp.rdata), UVM_HIGH);

   // Temporary hack to write the random number into ISS memory so that ISS can "see" the random number GPR register load as the RTL
   cv32e40p_cntxt.rvvi_memory_vif.mem[mon_trn.address >> 2] = slv_rsp.rdata;

   add_r_fields(mon_trn, slv_rsp);
   `uvm_send(slv_rsp)

endtask : vp_body

`endif // __UVME_CV32E40P_VP_RAND_NUM_SEQ_SV__
