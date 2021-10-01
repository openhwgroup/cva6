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


`ifndef __UVMA_OBI_SLV_VSEQ_SV__
`define __UVMA_OBI_SLV_VSEQ_SV__


/**
 * TODO Describe uvma_obi_slv_vseq_c
 */
class uvma_obi_slv_vseq_c extends uvma_obi_base_vseq_c;
   
   `uvm_object_utils(uvma_obi_slv_vseq_c)
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_slv_vseq");
   
   /**
    * TODO Describe uvma_obi_slv_vseq_c::body()
    */
   extern virtual task body();
   
   /**
    * TODO Describe uvma_obi_slv_vseq_c::respond_to_mstr()
    */
   extern virtual task respond_to_mstr(ref uvma_obi_slv_a_mon_trn_c slv_a_mon_trn);
   
endclass : uvma_obi_slv_vseq_c


function uvma_obi_slv_vseq_c::new(string name="uvma_obi_slv_vseq");
   
   super.new(name);
   
endfunction : new


task uvma_obi_slv_vseq_c::body();
   
   uvma_obi_slv_a_mon_trn_c  slv_a_mon_trn;
   
   forever begin
      p_sequencer.slv_r_mon_trn_fifo.peek_next_item(slv_a_mon_trn);
      if (slv_a_mon_trn) begin
         respond_to_mstr(slv_a_mon_trn);
      end
   end
   
endtask : body


task uvma_obi_slv_vseq_c::respond_to_mstr(ref uvma_obi_slv_a_mon_trn_c slv_a_mon_trn);
   
   uvma_obi_slv_a_seq_item_c  slv_a_seq_item;
   uvma_obi_slv_r_seq_item_c  slv_r_seq_item;
   
   /*`uvm_create_on(slv_a_seq_item, p_sequencer.slv_a_sequencer)
   `uvm_rand_send_with(slv_a_seq_item, {
      
   })
   p_sequencer.slv_r_mon_trn_fifo.peek_next_item(slv_a_mon_trn);
   `uvm_create_on(slv_r_seq_item, p_sequencer.slv_r_sequencer)
   `uvm_rand_send_with(slv_r_seq_item, {
      
   })*/
   
endtask : respond_to_mstr


`endif // __UVMA_OBI_BASE_SEQ_SV__
