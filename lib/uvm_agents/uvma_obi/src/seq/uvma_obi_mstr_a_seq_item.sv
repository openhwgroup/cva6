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


`ifndef __UVMA_OBI_MSTR_A_SEQ_ITEM_SV__
`define __UVMA_OBI_MSTR_A_SEQ_ITEM_SV__


/**
 * Object created by Open Bus Interface agent sequences extending uvma_obi_seq_base_c.
 */
class uvma_obi_mstr_a_seq_item_c extends uvml_seq_item_c;
   
   // Data
   rand bit                   req    ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::req
   rand uvma_obi_addr_b_t     addr   ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::addr
   rand bit                   we     ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::we
   rand uvma_obi_be_b_t       be     ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::be
   rand uvma_obi_data_b_t     wdata  ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::wdata
   rand uvma_obi_auser_b_t    auser  ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::auser
   rand uvma_obi_wuser_b_t    wuser  ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::wuser
   rand uvma_obi_id_b_t       aid    ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::aid
   rand uvma_obi_atop_b_t     atop   ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::atop
   rand uvma_obi_memtype_b_t  memtype; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::memtype
   rand uvma_obi_prot_b_t     prot   ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::prot
   rand bit                   reqpar ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::reqpar
   rand uvma_obi_achk_b_t     achk   ; ///< TODO Describe uvma_obi_mstr_a_seq_item_c::achk
   
   // Metadata
   uvma_obi_cfg_c  cfg; ///< Agent configuration handle
   
   
   `uvm_object_utils_begin(uvma_obi_mstr_a_seq_item_c)
      `uvm_field_int(req    , UVM_DEFAULT)
      `uvm_field_int(addr   , UVM_DEFAULT)
      `uvm_field_int(we     , UVM_DEFAULT)
      `uvm_field_int(be     , UVM_DEFAULT)
      `uvm_field_int(wdata  , UVM_DEFAULT)
      `uvm_field_int(auser  , UVM_DEFAULT)
      `uvm_field_int(wuser  , UVM_DEFAULT)
      `uvm_field_int(aid    , UVM_DEFAULT)
      `uvm_field_int(atop   , UVM_DEFAULT)
      `uvm_field_int(memtype, UVM_DEFAULT)
      `uvm_field_int(prot   , UVM_DEFAULT)
      `uvm_field_int(reqpar , UVM_DEFAULT)
      `uvm_field_int(achk   , UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   constraint default_cons {
      soft req !== reqpar;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mstr_a_seq_item");
   
endclass : uvma_obi_mstr_a_seq_item_c


function uvma_obi_mstr_a_seq_item_c::new(string name="uvma_obi_mstr_a_seq_item");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_OBI_MSTR_A_SEQ_ITEM_SV__
