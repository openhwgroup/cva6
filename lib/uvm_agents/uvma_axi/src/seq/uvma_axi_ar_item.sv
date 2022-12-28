// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 sequence item : Read Address channel  ****/


`ifndef __UVMA_AXI_AR_ITEM_SV__
`define __UVMA_AXI_AR_ITEM_SV__

class uvma_axi_ar_item_c extends uvm_sequence_item;

   rand logic [AXI_ID_WIDTH-1:0]   ar_id;
   rand logic [AXI_ADDR_WIDTH-1:0] ar_addr;
   rand logic [7:0]                ar_len;
   rand logic [2:0]                ar_size;
   rand logic [1:0]                ar_burst;
   rand logic [1:0]                ar_user;
   rand logic                      ar_valid;
   rand logic                      ar_ready;
   rand logic                      ar_lock;
   int                             ar_latency;

   `uvm_object_utils_begin(uvma_axi_ar_item_c)
      `uvm_field_int(ar_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_addr, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_len, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_size, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_burst, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_lock, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(ar_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);
   `uvm_object_utils_end

   function new(string name = "uvma_axi_ar_item_c");
      super.new(name);
   endfunction

endclass

`endif
