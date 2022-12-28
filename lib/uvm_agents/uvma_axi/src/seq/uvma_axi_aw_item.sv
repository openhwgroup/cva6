// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 sequence item : Write address channel ****/

`ifndef __UVMA_AXI_AW_ITEM_SV__
`define __UVMA_AXI_AW_ITEM_SV__


class uvma_axi_aw_item_c extends uvm_sequence_item;

   rand logic [AXI_ID_WIDTH-1:0]   aw_id;
   rand logic [AXI_ADDR_WIDTH-1:0] aw_addr;
   rand logic [AXI_USER_WIDTH-1:0] aw_user;
   rand logic [7:0]                aw_len;
   rand logic [2:0]                aw_size;
   rand logic [1:0]                aw_burst;
   rand logic                      aw_valid;
   rand logic                      aw_ready;
   rand logic [3:0]                aw_cache;
   rand logic                      aw_lock;
   rand logic [2:0]                aw_prot;
   rand logic [3:0]                aw_qos;
   rand logic [3:0]                aw_region;
   rand logic [5:0]                aw_atop;
   int                             aw_latency;

   `uvm_object_utils_begin(uvma_axi_aw_item_c)
      `uvm_field_int(aw_id, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_addr, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_len, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_size, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_burst, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_valid, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_ready, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_cache, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_user, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_lock, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_prot, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_qos, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_region, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_atop, UVM_ALL_ON | UVM_NOPACK);
      `uvm_field_int(aw_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE);
   `uvm_object_utils_end

   function new(string name = "uvma_axi_aw_item_c");
      super.new(name);
   endfunction

endclass

`endif
