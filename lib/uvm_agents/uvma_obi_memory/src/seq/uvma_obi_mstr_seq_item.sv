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


`ifndef __UVMA_OBI_MSTR_SEQ_ITEM_SV__
`define __UVMA_OBI_MSTR_SEQ_ITEM_SV__


/**
 * Object created by Open Bus Interface agent sequences extending
 * uvma_obi_mstr_seq_base_c.
 */
class uvma_obi_mstr_seq_item_c extends uvma_obi_base_seq_item_c;
   
   // Data
   rand uvma_obi_addr_b_t   address; ///< Read/Write Address
   rand uvma_obi_data_b_t   wdata  ; ///< Write Data
        uvma_obi_data_b_t   rdata  ; ///< Read Data
   rand uvma_obi_be_b_t     be     ; ///< Byte Enable. Is set for the bytes to write/read.
   rand uvma_obi_auser_b_t  auser  ; ///< Address Phase User signals. Valid for both read and write transactions.
   rand uvma_obi_wuser_b_t  wuser  ; ///< Additional Address Phase User signals. Only valid for write transactions.
   rand uvma_obi_ruser_b_t  ruser  ; ///< Response phase User signals. Only valid for read transactions. Undefined for write transactions.
   rand uvma_obi_id_b_t     id     ; ///< Address/Response Phase transaction identifier.
   
   // Metadata
   rand int unsigned  req_latency   ; ///< Number of cycles before req is asserted
   rand int unsigned  rready_latency; ///< Number of cycles before rready is asserted after rvalid has been asserted
   rand int unsigned  rready_hold   ; ///< Number of cycles to keep rready asserted after rvalid has been de-asserted
   rand int unsigned  tail_length   ; ///< Number of idle cycles after rready has been de-asserted
   
   
   `uvm_object_utils_begin(uvma_obi_mstr_seq_item_c)
      `uvm_field_int (                           address    , UVM_DEFAULT          )
      `uvm_field_int (                           wdata      , UVM_DEFAULT          )
      `uvm_field_int (                           rdata      , UVM_DEFAULT          )
      `uvm_field_int (                           be         , UVM_DEFAULT + UVM_BIN)
      `uvm_field_int (                           auser      , UVM_DEFAULT          )
      `uvm_field_int (                           wuser      , UVM_DEFAULT          )
      `uvm_field_int (                           ruser      , UVM_DEFAULT          )
      `uvm_field_int (                           id         , UVM_DEFAULT          )
      
      `uvm_field_int(req_latency   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(rready_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(rready_hold   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(tail_length   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
   `uvm_object_utils_end
   
   
   /**
    * Describe defaults_cons
    */
   constraint defaults_cons {
      /*soft*/ id             == __uid;
      /*soft*/ req_latency    == 0;
      /*soft*/ rready_latency == 0;
      /*soft*/ rready_hold    == 1;
      /*soft*/ tail_length    == 1;
      foreach (be[ii]) {
         /*soft*/ be[ii] == 1'b1;
      }
   }
   
   /**
    * Describe rules_cons
    */
   constraint rules_cons {
      mode == UVMA_OBI_MODE_MSTR;
      be   != '0;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mstr_seq_item");
   
endclass : uvma_obi_mstr_seq_item_c


function uvma_obi_mstr_seq_item_c::new(string name="uvma_obi_mstr_seq_item");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_OBI_MSTR_SEQ_ITEM_SV__
