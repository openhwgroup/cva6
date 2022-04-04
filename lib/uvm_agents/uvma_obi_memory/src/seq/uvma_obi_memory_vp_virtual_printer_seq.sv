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

`ifndef __UVMA_OBI_MEMORY_VP_VIRTUAL_PRINTER_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_VIRTUAL_PRINTER_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvma_obi_memory_vp_virtual_printer_seq_c extends uvma_obi_memory_vp_base_seq_c;

   localparam NUM_WORDS = 11;

   `uvm_object_utils_begin(uvma_obi_memory_vp_virtual_printer_seq_c)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_virtual_printer_seq_c");

   /**
    * Implement number of peripherals
    */
   extern virtual function int unsigned get_num_words();

   /**
    * Implement sequence that will return a random number
    */
   extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

endclass : uvma_obi_memory_vp_virtual_printer_seq_c


function uvma_obi_memory_vp_virtual_printer_seq_c::new(string name="uvma_obi_memory_vp_virtual_printer_seq_c");

   super.new(name);

endfunction : new

function int unsigned uvma_obi_memory_vp_virtual_printer_seq_c::get_num_words();

   return NUM_WORDS;

endfunction : get_num_words

task uvma_obi_memory_vp_virtual_printer_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;

   `uvm_create(slv_rsp)
   slv_rsp.orig_trn = mon_trn;

   if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'virtual_printer':\n%s", mon_trn.sprint()), UVM_DEBUG)
      // Allow $write as this acts as a UART/serial printer
      //@DVT_LINTER_WAIVER_START "SR20211012" disable SVTB.29.1.7
      $write("%c", mon_trn.data[7:0]);
      //@DVT_LINTER_WAIVER_END "SR20211012"
   end
   else if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      // If reading from virtual printer, simply return 0
      slv_rsp.rdata =0;
   end

   add_r_fields(mon_trn, slv_rsp);
   `uvm_send(slv_rsp)

endtask : vp_body

`endif // __UVMA_OBI_MEMORY_VP_VIRTUAL_PRINTER_SEQ_SV__
