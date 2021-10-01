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


`ifndef __UVMA_OBI_MSTR_R_MON_TRN_SV__
`define __UVMA_OBI_MSTR_R_MON_TRN_SV__


/**
 * Object rebuilt by the Open Bus Interface monitor.  Analog of uvma_obi_mstr_r_seq_item_c.
 */
class uvma_obi_mstr_r_mon_trn_c extends uvml_mon_trn_c;
   
   // Data
   logic  rready   ; ///< TODO Describe uvma_obi_mstr_r_mon_trn_c::rready
   logic  rreadypar; ///< TODO Describe uvma_obi_mstr_r_mon_trn_c::rreadypar
   
   // Metadata
   uvma_obi_cfg_c  cfg; ///< Agent configuration handle
   
   
   `uvm_object_utils_begin(uvma_obi_mstr_r_mon_trn_c)
      `uvm_field_int(rready   , UVM_DEFAULT)
      `uvm_field_int(rreadypar, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mstr_r_mon_trn");
   
endclass : uvma_obi_mstr_r_mon_trn_c


function uvma_obi_mstr_r_mon_trn_c::new(string name="uvma_obi_mstr_r_mon_trn");
   
   super.new(name);
   rready    = 0;
   rreadypar = 0;
   
endfunction : new


`endif // __UVMA_OBI_MSTR_R_MON_TRN_SV__
