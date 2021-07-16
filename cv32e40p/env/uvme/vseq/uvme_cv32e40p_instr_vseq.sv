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


`ifndef __UVME_CV32E40P_INSTR_VSEQ_SV__
`define __UVME_CV32E40P_INSTR_VSEQ_SV__


/**
 * Virtual sequence implementing the cv32e40p instruction memory.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvme_cv32e40p_instr_vseq_c extends uvme_cv32e40p_base_vseq_c;
   
   // Fields
   rand int unsigned  max_latency;
   string             mem_contents_location = "";
   
   
   `uvm_object_utils_begin(uvme_cv32e40p_instr_vseq_c)
      `uvm_field_int(max_latency, UVM_DEFAULT + UVM_DEC)
   `uvm_object_utils_end
   
   
   constraint defaults_cons {
      /*soft*/ max_latency == 10;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40p_instr_vseq");
   
   /**
    * TODO Describe uvme_cv32e40p_instr_vseq_c::body()
    */
   extern virtual task body();
   
endclass : uvme_cv32e40p_instr_vseq_c


function uvme_cv32e40p_instr_vseq_c::new(string name="uvme_cv32e40p_instr_vseq");

   int fd;

   super.new(name);
   if($value$plusargs("firmware=%s", mem_contents_location)) begin
     // First, check if it exists...
     fd = $fopen (mem_contents_location, "r");   
     if (fd)  `uvm_info ("OBI_MEMORY_SLV_SEQ", $sformatf("%s was opened successfully : (fd=%0d)", mem_contents_location, fd), UVM_LOW)
     else     `uvm_fatal("OBI_MEMORY_SLV_SEQ", $sformatf("%s was NOT opened successfully : (fd=%0d)", mem_contents_location, fd))
     $fclose(fd);
   end

endfunction : new


task uvme_cv32e40p_instr_vseq_c::body();
   
   uvma_obi_memory_mon_trn_c       mon_trn;
   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   bit                             error = 0;
   integer                         file;
   integer                         errno;
   string                          error_dscr;
   
   file = $fopen(mem_contents_location, "r");
   errno = $ferror(file, error_dscr);
   if (errno != 0) begin
      `uvm_warning("OBI_MEMORY_SLV_SEQ", $sformatf("Cannot open %s for reading (error description: %s).", mem_contents_location, error_dscr))
   end
   else begin 
      `uvm_info("OBI_MEMORY_SLV_SEQ", $sformatf("Loading memory contents from %s", mem_contents_location), UVM_LOW)
      $readmemh(mem_contents_location, cntxt.mem);
   end

   for (int jj=0; jj<32'h100; jj +=4) begin
      `uvm_info("OBI_MEMORY_SLV_SEQ", $sformatf("addr:%8h; data: %2h %2h %2h %2h", jj, cntxt.mem[jj+3], cntxt.mem[jj+2], cntxt.mem[jj+1], cntxt.mem[jj+0]), UVM_DEBUG)
   end
   
   forever begin
      // Wait for the monitor to send us the mstr's "req" with an access request
      p_sequencer.obi_memory_instr_sequencer.mon_trn_fifo.get(mon_trn);
      `uvm_info("OBI_MEMORY_SLV_SEQ", $sformatf("Got mon_trn:\n%s", mon_trn.sprint()), UVM_HIGH)
      
      error  = mon_trn.err;
      //error |= (mon_trn.address > (2**8));
      
      `uvm_create(slv_rsp)
      slv_rsp.err            = error;
      if (cntxt.instr_mem_delay_enabled) begin
         slv_rsp.gnt_latency    = $urandom_range(1,max_latency);
         slv_rsp.access_latency = $urandom_range(1,max_latency);
         slv_rsp.hold_duration  = $urandom_range(1,max_latency);
         slv_rsp.tail_length    = $urandom_range(1,max_latency);
      end
      else begin
         slv_rsp.gnt_latency    = 1;
         slv_rsp.access_latency = 1;
         slv_rsp.hold_duration  = 1;
         slv_rsp.tail_length    = 1;
      end
      
      if (!error) begin
         if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
            cntxt.mem[mon_trn.address] = mon_trn.data;
         end
         else begin
            slv_rsp.rdata[31:24] = cntxt.mem[mon_trn.address+3];
            slv_rsp.rdata[23:16] = cntxt.mem[mon_trn.address+2];
            slv_rsp.rdata[15:08] = cntxt.mem[mon_trn.address+1];
            slv_rsp.rdata[07:00] = cntxt.mem[mon_trn.address+0];
            `uvm_info("INSTR VSEQ", $sformatf("addr: %8h;  rdata: %8h", mon_trn.address, slv_rsp.rdata), UVM_NONE)
         end
      end
      else begin
         if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
            // TODO: need to figured out what a proper error response is
            slv_rsp.rdata = 32'hdead_beef;
         end
      end
      
      //slv_rsp.start(p_sequencer.obi_memory_instr_sqr);
      slv_rsp.set_sequencer(p_sequencer.obi_memory_instr_sequencer);
      `uvm_send(slv_rsp)
   end //forever
   
endtask : body

`endif // __UVME_CV32E40P_INSTR_VSEQ_SV__
