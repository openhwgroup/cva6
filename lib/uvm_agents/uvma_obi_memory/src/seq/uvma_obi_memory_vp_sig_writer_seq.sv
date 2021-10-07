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

`ifndef __UVMA_OBI_MEMORY_VP_SIG_WRITER_SEQ_SV__
`define __UVMA_OBI_MEMORY_VP_SIG_WRITER_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
virtual class uvma_obi_memory_vp_sig_writer_seq_c extends uvma_obi_memory_vp_base_seq_c;

   localparam    NUM_WORDS = 3;

   bit[31:0]     signature_start_address;
   bit[31:0]     signature_end_address;
   string        sig_file     = "";
   int           sig_fd       = 0;
   bit           use_sig_file = 0;

   `uvm_field_utils_begin(uvma_obi_memory_vp_sig_writer_seq_c)
      `uvm_field_int(signature_start_address, UVM_DEFAULT)
      `uvm_field_int(signature_end_address,   UVM_DEFAULT)
   `uvm_field_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_vp_sig_writer_seq_c");

   /**
    * Implement number of peripherals
    */
   extern virtual function int unsigned get_num_words();

   /**
    * Implement sequence that will return a random number
    */
   extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   /**
    * Set virtual exit in core
    */
   pure virtual task set_exit_valid();

endclass : uvma_obi_memory_vp_sig_writer_seq_c


function uvma_obi_memory_vp_sig_writer_seq_c::new(string name="uvma_obi_memory_vp_sig_writer_seq_c");

   super.new(name);


   if ($value$plusargs("signature=%s", sig_file)) begin
      sig_fd = $fopen(sig_file, "w");
      if (sig_fd == 0) begin
          `uvm_error("VP_VSEQ", $sformatf("Could not open file %s for writing", sig_file));
          use_sig_file = 0;
      end
      else begin
          use_sig_file = 1;
      end
   end

endfunction : new

function int unsigned uvma_obi_memory_vp_sig_writer_seq_c::get_num_words();

   return NUM_WORDS;

endfunction : get_num_words

task uvma_obi_memory_vp_sig_writer_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;

   `uvm_create  (slv_rsp)
   slv_rsp.orig_trn = mon_trn;
   slv_rsp.err = 1'b0;

   if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      case (get_vp_index(mon_trn))
         0: signature_start_address = mon_trn.data;
         1: signature_end_address = mon_trn.data;

         2: begin
            for (int unsigned ii=signature_start_address; ii<signature_end_address; ii += 4) begin
               `uvm_info("VP_SIG_WRITER", "Dumping signature", UVM_HIGH/*NONE*/)
               if (use_sig_file) begin
                  $fdisplay(sig_fd, "%x%x%x%x", cntxt.mem.read(ii+3),
                                                cntxt.mem.read(ii+2),
                                                cntxt.mem.read(ii+1),
                                                cntxt.mem.read(ii+0));
               end
               else begin
                  `uvm_info("VP_VSEQ", $sformatf("%x%x%x%x", cntxt.mem.read(ii+3),
                                                            cntxt.mem.read(ii+2),
                                                            cntxt.mem.read(ii+1),
                                                            cntxt.mem.read(ii+0)), UVM_HIGH/*NONE*/)
               end
            end

            set_exit_valid();
         end
      endcase
   end
   else if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      slv_rsp.rdata = 0;
   end

   add_r_fields(mon_trn, slv_rsp);
   slv_rsp.set_sequencer(p_sequencer);
   `uvm_send(slv_rsp)

endtask : vp_body

`endif // __UVMA_OBI_MEMORY_VP_SIG_WRITER_SEQ_SV__
