// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 sequence item : Write data channel****/

`ifndef __UVMA_AXI_W_ITEM_SV__
`define __UVMA_AXI_W_ITEM_SV__

class uvma_axi_w_item_c extends uvm_sequence_item;

   rand logic [AXI_DATA_WIDTH/8-1:0] w_strb;
   rand logic [AXI_DATA_WIDTH-1:0]   w_data;
   rand logic                        w_last;
   rand logic                        w_user;
   rand logic                        w_valid;
   rand logic                        w_ready;
   int                               w_latency;

   `uvm_object_param_utils_begin(uvma_axi_w_item_c)
      `uvm_field_int(w_strb, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_data, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_last, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(w_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);
   `uvm_object_utils_end

   function new(string name = "uvma_axi_w_item_c");
      super.new(name);
   endfunction

endclass

`endif
