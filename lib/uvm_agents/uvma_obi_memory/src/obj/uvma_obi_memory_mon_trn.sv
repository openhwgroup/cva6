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


`ifndef __UVMA_OBI_MEMORY_MON_TRN_SV__
`define __UVMA_OBI_MEMORY_MON_TRN_SV__


/**
 * Object rebuilt from the Open Bus Interface monitor Analog of
 * uvma_obi_base_seq_item_c.
 */
class uvma_obi_memory_mon_trn_c extends uvml_trn_mon_trn_c;

   // Data
   uvma_obi_memory_access_type_enum  access_type; ///< Read or write
   uvma_obi_memory_addr_l_t          address    ; ///< Read/Write Address
   uvma_obi_memory_data_l_t          data       ; ///< Read/Write Data
   uvma_obi_memory_be_l_t            be         ; ///< Byte Enable. Is set for the bytes to write/read.
   uvma_obi_memory_auser_l_t         auser      ; ///< Address Phase User signals. Valid for both read and write transactions. (1p2 only)
   uvma_obi_memory_wuser_l_t         wuser      ; ///< Additional Address Phase User signals. Only valid for write transactions. (1p2 only)
   uvma_obi_memory_ruser_l_t         ruser      ; ///< Response phase User signals. Only valid for read transactions. Undefined for write transactions. (1p2 only)
   uvma_obi_memory_id_l_t            aid        ; ///< Address Phase transaction identifier. (1p2 only)
   uvma_obi_memory_id_l_t            rid        ; ///< Address Phase transaction identifier. (1p2 only)
   uvma_obi_memory_err_l_t           err        ; ///< Error (1p2 only)
   uvma_obi_memory_exokay_l_t        exokay     ; ///< Exclusive access response (1p2 only)
   uvma_obi_memory_atop_l_t          atop       ; ///< Atomic attributes of transaction (1p2 only)
   uvma_obi_memory_memtype_l_t       memtype    ; ///< Bufferable and cacheable attributes of transactions (1p2 only)
   uvma_obi_memory_prot_l_t          prot       ; ///< Memory access type and privilege level of transaction
   uvma_obi_memory_achk_l_t          achk       ; ///< Address signal checksum
   uvma_obi_memory_rchk_l_t          rchk       ; ///< Response signal checksum

   // Metadata
   uvma_obi_memory_cfg_c  cfg           ; ///< Handle to agent's configuration object
   int unsigned           gnt_latency   ; ///< Number of cycles before gnt is asserted after req is asserted
   int unsigned           rvalid_latency; ///< Number of cycles before rvalid is asserted after gnt is asserted
   //int unsigned           rready_latency; ///< Number of cycles before rready is asserted after rvalid is asserted

   `uvm_object_utils_begin(uvma_obi_memory_mon_trn_c)
      `uvm_field_enum(uvma_obi_memory_access_type_enum, access_type, UVM_DEFAULT          )
      `uvm_field_int (                                  address    , UVM_DEFAULT          )
      `uvm_field_int (                                  data       , UVM_DEFAULT          )
      `uvm_field_int (                                  be         , UVM_DEFAULT + UVM_BIN)
      `uvm_field_int (                                  auser      , UVM_DEFAULT          )
      `uvm_field_int (                                  wuser      , UVM_DEFAULT          )
      `uvm_field_int (                                  ruser      , UVM_DEFAULT          )
      `uvm_field_int (                                  aid        , UVM_DEFAULT          )
      `uvm_field_int (                                  rid        , UVM_DEFAULT          )
      `uvm_field_int (                                  err        , UVM_DEFAULT          )
      `uvm_field_int (                                  atop       , UVM_DEFAULT          )
      `uvm_field_int (                                  memtype    , UVM_DEFAULT          )
      `uvm_field_int (                                  prot       , UVM_DEFAULT          )
      `uvm_field_int (                                  achk       , UVM_DEFAULT          )
      `uvm_field_int (                                  rchk       , UVM_DEFAULT          )

      `uvm_field_int(gnt_latency   , UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
      `uvm_field_int(rvalid_latency, UVM_DEFAULT + UVM_DEC + UVM_NOCOMPARE)
   `uvm_object_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_memory_mon_trn");

   /**
    * Fetch mask for printing
    */
   extern function uvma_obi_memory_data_l_t get_be_bitmask();

   /**
    * Print data with -- for non transmitted bytes
    */
   extern function string get_data_str();

endclass : uvma_obi_memory_mon_trn_c


function uvma_obi_memory_mon_trn_c::new(string name="uvma_obi_memory_mon_trn");

   super.new(name);

endfunction : new


function uvma_obi_memory_data_l_t uvma_obi_memory_mon_trn_c::get_be_bitmask();

   uvma_obi_memory_data_l_t bitmask = '0;

   for (int i = 0; i < cfg.data_width / 8; i++) begin
      if (be[i]) bitmask |= 'hff << (i*8);
   end

   return bitmask;

endfunction : get_be_bitmask

function string uvma_obi_memory_mon_trn_c::get_data_str();

   uvma_obi_memory_data_l_t be_bitmask = this.get_be_bitmask();
   string data_str;

   for (int i = 0; i < cfg.data_width / 8; i++) begin
      if (be[i])
         data_str = $sformatf("%02x%s", this.data[i*8+:8], data_str);
      else
         data_str = $sformatf("--%s", data_str);
   end

   return data_str;

endfunction : get_data_str

`endif // __UVMA_OBI_MEMORY_MON_TRN_SV__
