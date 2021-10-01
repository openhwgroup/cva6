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


`ifndef __UVMA_OBI_MSTR_VSEQ_SV__
`define __UVMA_OBI_MSTR_VSEQ_SV__


/**
 * TODO Describe uvma_obi_mstr_vseq_c
 */
class uvma_obi_mstr_vseq_c extends uvma_obi_base_vseq_c;
   
   `uvm_object_utils(uvma_obi_mstr_vseq_c)
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mstr_vseq");
   
   /**
    * TODO Describe uvma_obi_mstr_vseq_c::body()
    */
   extern virtual task body();
   
   /**
    * TODO Describe uvma_obi_mstr_vseq_c::do_bus_operation()
    */
   extern virtual do_bus_operation(ref uvma_obi_seq_item_c seq_item);
   
endclass : uvma_obi_mstr_vseq_c


function uvma_obi_mstr_vseq_c::new(string name="uvma_obi_mstr_vseq");
   
   super.new(name);
   
endfunction : new


task uvma_obi_mstr_vseq_c::body();
   
   uvma_obi_seq_item_c  seq_item;
   
   forever begin
      p_sequencer.get_next_item    (seq_item);
      do_bus_operation             (seq_item);
      p_sequencer.seq_item_ap.write(seq_item);
      p_sequencer.item_done();
   end
   
endtask : body


task uvma_obi_mstr_vseq_c::do_bus_operation(ref uvma_obi_seq_item_c seq_item);

   uvma_obi_mstr_a_seq_item_c  mstr_a_seq_item;
   uvma_obi_mstr_r_seq_item_c  mstr_r_seq_item;
   
   do begin
      `uvm_create_on(mstr_a_seq_item, p_sequencer.mstr_a_sequencer)
      `uvm_rand_send_with(mstr_a_seq_item, {
         req     == 1'b1;
         addr    == seq_item.address;
         we      == seq_item.access_type;
         be      == seq_item.be;
         wdata   == seq_item.data;
         auser   == seq_item.auser;
         wuser   == seq_item.wuser;
         aid     == seq_item.id;
         atop    == seq_item.atop;
         memtype == seq_item.memtype;
         prot    == seq_item.prot;
      })
   end while(cntxt.vif.gnt !== 1'b1);
   
   do begin
      `uvm_create_on(mstr_r_seq_item, p_sequencer.mstr_r_sequencer)
      `uvm_rand_send_with(mstr_r_seq_item, {
         rready == 1'b1;
      })
   end while(cntxt.vif.rvalid !== 1'b1);
   
   if (seq_item.access_type == UVMA_OBI_ACCESS_READ) begin
      seq_item.data = cntxt.vif.rdata;
   end
   
endtask : do_bus_operation


`endif // __UVMA_OBI_BASE_SEQ_SV__
