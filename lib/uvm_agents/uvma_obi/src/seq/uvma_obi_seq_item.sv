// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// Copyright 2021 Silicon Labs
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef __UVMA_OBI_SEQ_ITEM_SV__
`define __UVMA_OBI_SEQ_ITEM_SV__


/**
 * Object created by Open Bus Interface agent sequences extending uvma_obi_seq_base_c.
 */
class uvma_obi_seq_item_c extends uvml_seq_item_c;
   
   // Data
   rand uvma_obi_access_type_enum  access_type; ///< Read or write
   rand uvma_obi_addr_b_t          address    ; ///< Read/Write Address
   rand uvma_obi_data_b_t          data       ; ///< Write Data
   rand uvma_obi_be_b_t            be         ; ///< Byte Enable. Is set for the bytes to write/read.
   rand uvma_obi_auser_b_t         auser      ; ///< Address Phase User signals. Valid for both read and write transactions.
   rand uvma_obi_wuser_b_t         wuser      ; ///< Additional Address Phase User signals. Only valid for write transactions.
   rand uvma_obi_ruser_b_t         ruser      ; ///< Response phase User signals. Only valid for read transactions. Undefined for write transactions.
   rand uvma_obi_id_b_t            id         ; ///< Address/Response Phase transaction identifier.
   rand uvma_obi_atop_b_t          atop       ; ///< TODO Describe uvma_obi_seq_item_c::atop
   rand uvma_obi_memtype_b_t       memtype    ; ///< TODO Describe uvma_obi_seq_item_c::memtype
   rand uvma_obi_prot_b_t          prot       ; ///< TODO Describe uvma_obi_seq_item_c::prot
   
   // Metadata
   uvma_obi_cfg_c  cfg;
   
   // Metadata
   rand int unsigned  req_latency   ; ///< Number of cycles before req is asserted
   rand int unsigned  rready_latency; ///< Number of cycles before rready is asserted after rvalid has been asserted
   rand int unsigned  rready_hold   ; ///< Number of cycles to keep rready asserted after rvalid has been de-asserted
   rand int unsigned  tail_length   ; ///< Number of idle cycles after rready has been de-asserted
   
   
   `uvm_object_utils_begin(uvma_obi_seq_item_c)
      `uvm_field_enum(uvma_obi_access_type_enum, access_type, UVM_DEFAULT          )
      `uvm_field_int (                           address    , UVM_DEFAULT          )
      `uvm_field_int (                           data       , UVM_DEFAULT          )
      `uvm_field_int (                           be         , UVM_DEFAULT + UVM_BIN)
      `uvm_field_int (                           auser      , UVM_DEFAULT          )
      `uvm_field_int (                           wuser      , UVM_DEFAULT          )
      `uvm_field_int (                           ruser      , UVM_DEFAULT          )
      `uvm_field_int (                           id         , UVM_DEFAULT          )
      `uvm_field_int (                           atop       , UVM_DEFAULT          )
      `uvm_field_int (                           memtype    , UVM_DEFAULT          )
      `uvm_field_int (                           prot       , UVM_DEFAULT          )
      
      `uvm_field_int(req_latency   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(rready_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(rready_hold   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(tail_length   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
   `uvm_object_utils_end
   
   
   // TODO Add uvma_obi_seq_item_c constraints
   //      Ex: constraint default_cons {
   //             abc inside {0,2,4,8,16,32};
   //          }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_seq_item");
   
endclass : uvma_obi_seq_item_c


function uvma_obi_seq_item_c::new(string name="uvma_obi_seq_item");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_OBI_SEQ_ITEM_SV__
