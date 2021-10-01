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


`ifndef __UVMA_OBI_SLV_A_SEQ_ITEM_SV__
`define __UVMA_OBI_SLV_A_SEQ_ITEM_SV__


/**
 * Object created by sequences running on uvma_obi_slv_a_sqr_c.
 */
class uvma_obi_slv_a_seq_item_c extends uvml_seq_item_c;
   
   // Data
   rand bit  gnt   ; ///< TODO Describe uvma_obi_slv_a_seq_item_c::gnt
   rand bit  gntpar; ///< TODO Describe uvma_obi_slv_a_seq_item_c::gntpar
   
   // Metadata
   uvma_obi_cfg_c  cfg; ///< Agent configuration handle
   
   
   `uvm_object_utils_begin(uvma_obi_slv_a_seq_item_c)
      `uvm_field_int(gnt   , UVM_DEFAULT)
      `uvm_field_int(gntpar, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   constraint default_cons {
      soft gnt != gntpar;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_slv_a_seq_item");
   
endclass : uvma_obi_slv_a_seq_item_c


function uvma_obi_slv_a_seq_item_c::new(string name="uvma_obi_slv_a_seq_item");
   
   super.new(name);
   
endfunction : new


`endif // __UVMA_OBI_SLV_A_SEQ_ITEM_SV__
