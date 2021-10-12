// Copyright 2021 OpenHW Group
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVMA_PMA_MON_TRN_SV__
`define __UVMA_PMA_MON_TRN_SV__


/**
 * Object rebuilt from the Memory attribution agent for OpenHW Group CORE-V verification testbenches monitor.  Analog of uvma_pma_seq_item_c.
 */
class uvma_pma_mon_trn_c#(int ILEN=DEFAULT_ILEN,
                          int XLEN=DEFAULT_XLEN) extends uvml_trn_mon_trn_c;

   // Metadata
   uvma_pma_cfg_c#(ILEN,XLEN)  cfg;

   // PMA region index
   int unsigned region_index;

   // Alternatively set the default region if the address does not map into
   // any PMA region
   // Note that this means it is either mppping to a deconfigured PMA (cfg.regions.size() == 0)
   // or the default PMA region (cfg.regions.size() != 0)
   bit is_default;

   // Access type (instruction or data)
   uvma_pma_access_enum access;

   // Set if the first word of the PMA region (for fucntional coverage)
   bit is_first_word;

   // Set if the last word of the PMA region (for functional coverage)
   bit is_last_word;

   // Read or write
   uvma_pma_rw_enum rw;

   `uvm_object_param_utils_begin(uvma_pma_mon_trn_c#(ILEN,XLEN))
      `uvm_field_int(                       region_index,  UVM_DEFAULT)
      `uvm_field_int(                       is_default,    UVM_DEFAULT)
      `uvm_field_enum(uvma_pma_access_enum, access,        UVM_DEFAULT)
      `uvm_field_enum(uvma_pma_rw_enum,     rw,            UVM_DEFAULT)
      `uvm_field_int(                       is_first_word, UVM_DEFAULT)
      `uvm_field_int(                       is_last_word,  UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_pma_mon_trn");

endclass : uvma_pma_mon_trn_c


function uvma_pma_mon_trn_c::new(string name="uvma_pma_mon_trn");

   super.new(name);

endfunction : new


`endif // __UVMA_PMA_MON_TRN_SV__
