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


`ifndef __UVMA_OBI_SLV_SEQ_ITEM_SV__
`define __UVMA_OBI_SLV_SEQ_ITEM_SV__


/**
 * Object created by Open Bus Interface agent sequences extending
 * uvma_obi_slv_seq_base_c.
 */
class uvma_obi_slv_seq_item_c extends uvma_obi_base_seq_item_c;
   
   // Data
   rand uvma_obi_data_b_t   rdata; ///< Read data.
   rand uvma_obi_ruser_b_t  ruser; ///< Response phase User signals. Only valid for read transactions. Undefined for write transactions.
   rand uvma_obi_id_b_t     rid  ; ///< Response Phase transaction identifier.
   rand bit                 err  ; ///< Error.
   
   // Metadata
   rand int unsigned   gnt_latency   ; ///< Measured in clock cycles
   rand int unsigned   access_latency; ///< Measured in clock cycles
   rand int unsigned   hold_duration ; ///< Measured in clock cycles
   rand int unsigned   tail_length   ; ///< Measured in clock cycles
   uvma_obi_mon_trn_c  orig_trn      ; ///< Monitored transaction to which this seq_item is responding
   
   
   `uvm_object_utils_begin(uvma_obi_slv_seq_item_c)
      `uvm_field_int(rdata , UVM_DEFAULT)
      `uvm_field_int(ruser , UVM_DEFAULT)
      `uvm_field_int(rid   , UVM_DEFAULT)
      `uvm_field_int(err   , UVM_DEFAULT)
      
      `uvm_field_int(gnt_latency   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(access_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(hold_duration , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(tail_length   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      
      `uvm_field_object(orig_trn, UVM_DEFAULT + UVM_NOCOMPARE)
   `uvm_object_utils_end
   
   
   constraint defaults_cons {
      /*soft*/ err            == 0;
      /*soft*/ gnt_latency    == 1;
      /*soft*/ access_latency == 1;
      /*soft*/ hold_duration  == 1;
      /*soft*/ tail_length    == 1;
   }
   
   /**
    * Describe rules_cons
    */
   constraint rules_cons {
      mode == UVMA_OBI_MODE_SLV;
   }

   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_slv_seq_item");
   
endclass : uvma_obi_slv_seq_item_c


function uvma_obi_slv_seq_item_c::new(string name="uvma_obi_slv_seq_item");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_OBI_SLV_SEQ_ITEM_SV__
