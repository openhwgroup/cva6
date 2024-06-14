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


`ifndef __UVME_OBI_SLV_SEQ_SV__
`define __UVME_OBI_SLV_SEQ_SV__


/**
 * Virtual sequence implementing the cva6 virtual peripherals.
 */
class uvme_obi_slv_seq_c extends uvma_obi_memory_slv_seq_c;


   `uvm_object_utils_begin(uvme_obi_slv_seq_c)
   `uvm_object_utils_end

   function new(string name="uvme_obi_slv_seq_c");
      super.new(name);
   endfunction : new
   
   
   task do_mem_operation(ref uvma_obi_memory_mon_trn_c mon_req);
      bit [31:0] word_aligned_addr;

      uvma_obi_memory_slv_seq_item_c  slv_rsp;
      `uvm_create(slv_rsp)
      slv_rsp.orig_trn = mon_req;
      slv_rsp.access_type = mon_req.access_type;

      word_aligned_addr = { mon_req.address[31:3], 3'h0 };

      `uvm_info("SLV_SEQ", $sformatf("Performing operation:\n%s", mon_req.sprint()), UVM_HIGH)
      if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
         if (mon_req.be[7]) cntxt.mem.write(word_aligned_addr+7, mon_req.data[63:56]);
         if (mon_req.be[6]) cntxt.mem.write(word_aligned_addr+6, mon_req.data[55:48]);
         if (mon_req.be[5]) cntxt.mem.write(word_aligned_addr+5, mon_req.data[47:40]);
         if (mon_req.be[4]) cntxt.mem.write(word_aligned_addr+4, mon_req.data[39:32]);
         if (mon_req.be[3]) cntxt.mem.write(word_aligned_addr+3, mon_req.data[31:24]);
         if (mon_req.be[2]) cntxt.mem.write(word_aligned_addr+2, mon_req.data[23:16]);
         if (mon_req.be[1]) cntxt.mem.write(word_aligned_addr+1, mon_req.data[15:08]);
         if (mon_req.be[0]) cntxt.mem.write(word_aligned_addr+0, mon_req.data[07:00]);
      end
      else begin
         if (mon_req.be[7]) slv_rsp.rdata[63:56] = cntxt.mem.read(word_aligned_addr+7);
         if (mon_req.be[6]) slv_rsp.rdata[55:48] = cntxt.mem.read(word_aligned_addr+6);
         if (mon_req.be[5]) slv_rsp.rdata[47:40] = cntxt.mem.read(word_aligned_addr+5);
         if (mon_req.be[4]) slv_rsp.rdata[39:32] = cntxt.mem.read(word_aligned_addr+4);
         if (mon_req.be[3]) slv_rsp.rdata[31:24] = cntxt.mem.read(word_aligned_addr+3);
         if (mon_req.be[2]) slv_rsp.rdata[23:16] = cntxt.mem.read(word_aligned_addr+2);
         if (mon_req.be[1]) slv_rsp.rdata[15:08] = cntxt.mem.read(word_aligned_addr+1);
         if (mon_req.be[0]) slv_rsp.rdata[07:00] = cntxt.mem.read(word_aligned_addr+0);
      end

      add_r_fields(mon_req, slv_rsp);
      slv_rsp.set_sequencer(p_sequencer);
      `uvm_send(slv_rsp)

   endtask : do_mem_operation


endclass : uvme_obi_slv_seq_c
`endif // __UVME_OBI_SLV_SEQ_SV__
