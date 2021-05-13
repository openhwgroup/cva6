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


`ifndef __UVMA_OBI_MON_TRN_SV__
`define __UVMA_OBI_MON_TRN_SV__


/**
 * Object rebuilt from the Open Bus Interface monitor Analog of
 * uvma_obi_base_seq_item_c.
 */
class uvma_obi_mon_trn_c extends uvml_trn_mon_trn_c;
   
   // Data
   uvma_obi_access_type_enum  access_type; ///< Read or write
   uvma_obi_addr_l_t          address    ; ///< Read/Write Address
   uvma_obi_data_l_t          data       ; ///< Read/Write Data
   uvma_obi_be_l_t            be         ; ///< Byte Enable. Is set for the bytes to write/read.
   uvma_obi_auser_l_t         auser      ; ///< Address Phase User signals. Valid for both read and write transactions.
   uvma_obi_wuser_l_t         wuser      ; ///< Additional Address Phase User signals. Only valid for write transactions.
   uvma_obi_ruser_l_t         ruser      ; ///< Response phase User signals. Only valid for read transactions. Undefined for write transactions.
   uvma_obi_id_l_t            id         ; ///< Address/Response Phase transaction identifier.
   bit                        err        ; ///< Error
   
   // Metadata
   int unsigned  gnt_latency   ; ///< Number of cycles before gnt is asserted after req is asserted
   int unsigned  rvalid_latency; ///< Number of cycles before rvalid is asserted after gnt is asserted
   int unsigned  rready_latency; ///< Number of cycles before rready is asserted after rvalid is asserted
   int unsigned  rp_hold       ; ///< Length of RP phase (in clk cycles)
   
   // Parameters
   int unsigned  auser_width;
   int unsigned  wuser_width;
   int unsigned  ruser_width;
   int unsigned  addr_width ;
   int unsigned  data_width ;
   int unsigned  id_width   ;
   
   
   `uvm_object_utils_begin(uvma_obi_mon_trn_c)
      `uvm_field_enum(uvma_obi_access_type_enum, access_type, UVM_DEFAULT          )
      `uvm_field_int (                           address    , UVM_DEFAULT          )
      `uvm_field_int (                           data       , UVM_DEFAULT          )
      `uvm_field_int (                           be         , UVM_DEFAULT + UVM_BIN)
      `uvm_field_int (                           auser      , UVM_DEFAULT          )
      `uvm_field_int (                           wuser      , UVM_DEFAULT          )
      `uvm_field_int (                           ruser      , UVM_DEFAULT          )
      `uvm_field_int (                           id         , UVM_DEFAULT          )
      `uvm_field_int (                           err        , UVM_DEFAULT          )
      
      `uvm_field_int(gnt_latency   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(rvalid_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(rready_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(rp_hold       , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mon_trn");
   
endclass : uvma_obi_mon_trn_c


function uvma_obi_mon_trn_c::new(string name="uvma_obi_mon_trn");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_OBI_MON_TRN_SV__
