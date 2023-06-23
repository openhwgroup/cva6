// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 sequence item : Read data channel  ****/

`ifndef __UVMA_AXI_R_ITEM_SV__
`define __UVMA_AXI_R_ITEM_SV__

class uvma_axi_r_item_c extends uvm_sequence_item;

   rand logic [AXI_ID_WIDTH-1:0]   r_id;
   rand logic [AXI_ADDR_WIDTH-1:0] r_data;
   rand logic [1:0]                r_resp;
   rand logic                      r_last;
   rand logic                      r_user;
   rand logic                      r_valid;
   logic                           r_ready;

   `uvm_object_utils_begin(uvma_axi_r_item_c)
      `uvm_field_int(r_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_data, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_resp, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_last, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(r_ready, UVM_ALL_ON | UVM_NOPACK);
  `uvm_object_utils_end

  function new(string name = "uvma_axi_r_item_c");
     super.new(name);
  endfunction

endclass

`endif
