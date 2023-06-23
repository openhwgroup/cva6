// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 sequence item : Write response channel ****/

`ifndef __UVMA_AXI_B_ITEM_SV__
`define __UVMA_AXI_B_ITEM_SV__

class uvma_axi_b_item_c extends uvm_sequence_item;

   rand logic [AXI_ID_WIDTH-1:0] b_id;
   rand logic [1:0]              b_resp;
   rand logic [1:0]              b_user;
   rand logic                    b_valid;
   rand logic                    b_ready;

   `uvm_object_param_utils_begin(uvma_axi_b_item_c)
      `uvm_field_int(b_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_resp, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(b_ready, UVM_ALL_ON | UVM_NOPACK);
   `uvm_object_utils_end

   function new(string name = "uvma_axi_b_item_c");
      super.new(name);
   endfunction

endclass

`endif


