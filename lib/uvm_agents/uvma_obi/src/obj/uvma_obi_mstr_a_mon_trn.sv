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


`ifndef __UVMA_OBI_MSTR_A_MON_TRN_SV__
`define __UVMA_OBI_MSTR_A_MON_TRN_SV__


/**
 * Object rebuilt by the Open Bus Interface monitor's A Channel Master.  Analog of uvma_obi_mstr_a_seq_item_c.
 */
class uvma_obi_mstr_a_mon_trn_c extends uvml_mon_trn_c;
   
   // Data
   logic                 req    ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::req
   uvma_obi_addr_l_t     addr   ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::addr
   logic                 we     ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::we
   uvma_obi_be_l_t       be     ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::be
   uvma_obi_data_l_t     wdata  ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::wdata
   uvma_obi_auser_l_t    auser  ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::auser
   uvma_obi_wuser_l_t    wuser  ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::wuser
   uvma_obi_id_l_t       aid    ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::aid
   uvma_obi_atop_l_t     atop   ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::atop
   uvma_obi_memtype_l_t  memtype; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::memtype
   uvma_obi_prot_l_t     prot   ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::prot
   logic                 reqpar ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::reqpar
   uvma_obi_achk_l_t     achk   ; ///< TODO Describe uvma_obi_mstr_a_mon_trn_c::achk
   
   // Metadata
   uvma_obi_cfg_c  cfg; ///< Agent configuration handle
   
   
   `uvm_object_utils_begin(uvma_obi_mstr_a_mon_trn_c)
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
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mstr_a_mon_trn");
   
endclass : uvma_obi_mstr_a_mon_trn_c


function uvma_obi_mstr_a_mon_trn_c::new(string name="uvma_obi_mstr_a_mon_trn");
   
   super.new(name);
   req     = 0;
   addr    = 0;
   we      = 0;
   be      = 0;
   wdata   = 0;
   auser   = 0;
   wuser   = 0;
   aid     = 0;
   atop    = 0;
   memtype = 0;
   prot    = 0;
   reqpar  = 0;
   achk    = 0;
   
endfunction : new


`endif // __UVMA_OBI_MSTR_A_MON_TRN_SV__
