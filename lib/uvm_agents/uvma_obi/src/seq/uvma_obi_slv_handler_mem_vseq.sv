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


`ifndef __UVMA_OBI_SLV_HANDLER_MEM_VSEQ_SV__
`define __UVMA_OBI_SLV_HANDLER_MEM_VSEQ_SV__


/**
 * TODO Describe uvma_obi_slv_handler_mem_vseq_c
 */
class uvma_obi_slv_handler_mem_vseq_c extends uvma_obi_slv_handler_base_vseq_c;
   
   `uvm_object_utils(uvma_obi_slv_handler_mem_vseq_c)
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_slv_handler_mem_vseq");
   
   /**
    * TODO Describe uvma_obi_slv_handler_mem_vseq_c::body()
    */
   extern virtual task body();
   
   /**
    * TODO Describe uvma_obi_slv_handler_mem_vseq_c::body()
    */
   extern virtual task handle_mstr_req(ref uvma_obi_mstr_a_mon_trn_c trn, output bit handled=0);
   
endclass : uvma_obi_slv_handler_mem_vseq_c


function uvma_obi_slv_handler_mem_vseq_c::new(string name="uvma_obi_slv_handler_mem_vseq");
   
   super.new(name);
   
endfunction : new


task uvma_obi_slv_handler_mem_vseq_c::body();
   
   p_sequencer.cntxt.slv_handlers.push_back(this);
   forever begin
      wait (cntxt.vif.clk === 1'b1);
   end
   
endtask : body


task uvma_obi_slv_handler_mem_vseq_c::handle_mstr_req(ref uvma_obi_mstr_a_mon_trn_c trn, output bit handled=0);
   
   uvma_obi_data_b_t  readback_data;
   
   // TODO Add response latency cycles
   
   do begin
      `uvm_create_on(slv_r_seq_item, p_sequencer.slv_r_sequencer)
      
      if (mon_trn.we === 1'b1) begin
         mem_write(trn.addr, trn.data);
         `uvm_rand_send_with(slv_r_seq_item, {
            rvalid == 1'b1;
            err    == 1'b0;
            ruser  == mon_trn.auser;
            rid    == mon_trn.aid  ;
            // TODO Implement exokay
            // TODO Implement rchk
         })
      end
      else begin
         readback_data = mem_read(trn.addr);
         `uvm_rand_send_with(slv_r_seq_item, {
            rvalid == 1'b1;
            rdata  == readback_data;
            err    == 1'b0;
            ruser  == mon_trn.auser;
            rid    == mon_trn.aid  ;
            // TODO Implement exokay
            // TODO Implement rchk
         })
      end
      peek_mstr_r_mon_trn(mon_trn);
   end while (mon_r_trn.rready !== 1'b1);
   
   handled = 1;
   
endtask : body


`endif // __UVMA_OBI_SLV_HANDLER_MEM_VSEQ_SV__
