// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)


`ifndef __UVMA_AXI_FW_PRELOAD_SEQ_SV__
`define __UVMA_AXI_FW_PRELOAD_SEQ_SV__


/**
 * Virtual sequence implementing the cv32e40x virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvma_axi_fw_preload_seq_c extends uvm_sequence;

   static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();
            // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   uvml_mem_c mem;

   bit[63:0] value;
   logic [7:0][7:0] mem_row;
   string binary = "";
   longint address;
   longint len;
   byte buffer[];
   
   `uvm_object_utils(uvma_axi_fw_preload_seq_c)
   `uvm_declare_p_sequencer(uvma_axi_r_sqr_c)
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_fw_preload_seq");
   

   extern virtual task body();
   
endclass : uvma_axi_fw_preload_seq_c

function uvma_axi_fw_preload_seq_c::new(string name="uvma_axi_fw_preload_seq");
   
   super.new(name);
   mem = uvml_mem_c::type_id::create("mem");

endfunction : new

task uvma_axi_fw_preload_seq_c::body();

   cfg   = p_sequencer.cfg  ;
   void'(uvcl.get_arg_value("+PRELOAD=", binary));

   if (binary != "") begin
      void'(read_elf(binary));
      wait(p_sequencer.cntxt.axi_vi.clk);
      // while there are more sections to process
      while (get_section(address, len)) begin
         automatic int num_words0 = (len+7)/8;
         `uvm_info( "Core Test", $sformatf("Loading Address: %x, Length: %x", address, len), UVM_HIGH)
         buffer = new [num_words0*8];
         void'(read_section(address, buffer));
         // preload memories
         // 64-bit
         for (int i = 0; i < num_words0; i++) begin
            mem_row = '0;
            for (int j = 0; j < 8; j++) begin
                mem_row[j] = buffer[i*8 + j];
            end
            mem.write(address + i*8 + 0, mem_row[0]);
            mem.write(address + i*8 + 1, mem_row[1]);
            mem.write(address + i*8 + 2, mem_row[2]);
            mem.write(address + i*8 + 3, mem_row[3]);
            mem.write(address + i*8 + 4, mem_row[4]);
            mem.write(address + i*8 + 5, mem_row[5]);
            mem.write(address + i*8 + 6, mem_row[6]);
            mem.write(address + i*8 + 7, mem_row[7]);
         end
          p_sequencer.cntxt.mem = mem;
      end
   end

endtask : body

`endif // __UVMA_AXI_FW_PRELOAD_SEQ_SV__
