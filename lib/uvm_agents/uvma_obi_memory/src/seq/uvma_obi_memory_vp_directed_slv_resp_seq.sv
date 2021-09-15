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

`ifndef __UVMA_OBI_MEMORY_VP_DIRECTED_SLV_RESP_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_DIRECTED_SLV_RESP_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvma_obi_memory_vp_directed_slv_resp_seq_c#(OBI_PERIPHS=1) extends uvma_obi_memory_vp_base_seq_c;

   localparam ERR_ADDR_MIN_INDEX    = 0;
   localparam ERR_ADDR_MAX_INDEX    = 1;
   localparam ERR_VALID_INDEX       = 2;

   localparam EXOKAY_ADDR_MIN_INDEX = 3;
   localparam EXOKAY_ADDR_MAX_INDEX = 4;
   localparam EXOKAY_VALID_INDEX    = 5;

   localparam WORDS_PER_OBI = EXOKAY_VALID_INDEX + 1;

   // An array of OBI memory configurations
   // This enables a single set of virtual peripheral registers (6*OBI_PERIPHS) to control
   // OBI_PERIPHS number of OBIs 
   // For example, in a typical OBI-I, OBI-D configuration, only the OBI-D is writable
   // but we would also need to control the OBI-I as well
   uvma_obi_memory_cfg_c obi_cfg[];

   `uvm_object_param_utils_begin(uvma_obi_memory_vp_directed_slv_resp_seq_c#(OBI_PERIPHS))
   `uvm_object_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_directed_slv_resp_seq_c");

   /**
    * Implement number of peripherals
    */
   extern virtual function int unsigned get_num_words();

   /**
    * Implement sequence that will return a random number
    */
   extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);


endclass : uvma_obi_memory_vp_directed_slv_resp_seq_c

function uvma_obi_memory_vp_directed_slv_resp_seq_c::new(string name="uvma_obi_memory_vp_directed_slv_resp_seq_c");
   
   super.new(name);
   
   obi_cfg = new[OBI_PERIPHS];

endfunction : new

function int unsigned uvma_obi_memory_vp_directed_slv_resp_seq_c::get_num_words();
   
   return WORDS_PER_OBI * OBI_PERIPHS;

endfunction : get_num_words

task uvma_obi_memory_vp_directed_slv_resp_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   int unsigned obi_index;

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   `uvm_create(slv_rsp)
   
   slv_rsp.orig_trn = mon_trn;
   slv_rsp.err = 1'b0;

   obi_index = get_vp_index(mon_trn) / WORDS_PER_OBI;
   case (get_vp_index(mon_trn) % WORDS_PER_OBI)
      ERR_ADDR_MIN_INDEX:    obi_cfg[obi_index].directed_slv_err_addr_min    = slv_rsp.orig_trn.data;
      ERR_ADDR_MAX_INDEX:    obi_cfg[obi_index].directed_slv_err_addr_max    = slv_rsp.orig_trn.data;
      ERR_VALID_INDEX:       obi_cfg[obi_index].directed_slv_err_valid       = slv_rsp.orig_trn.data[0];
      EXOKAY_ADDR_MIN_INDEX: obi_cfg[obi_index].directed_slv_exokay_addr_min = slv_rsp.orig_trn.data;
      EXOKAY_ADDR_MAX_INDEX: obi_cfg[obi_index].directed_slv_exokay_addr_max = slv_rsp.orig_trn.data;
      EXOKAY_VALID_INDEX:    obi_cfg[obi_index].directed_slv_exokay_valid    = slv_rsp.orig_trn.data[0];
   endcase

   add_r_fields(mon_trn, slv_rsp);
   slv_rsp.set_sequencer(p_sequencer);
   `uvm_send(slv_rsp)

endtask : vp_body

`endif // __UVMA_OBI_MEMORY_VP_DIRECTED_SLV_RESP_SEQ_SV__


