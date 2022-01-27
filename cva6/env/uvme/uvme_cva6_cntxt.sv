// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
// Copyright 2021 Thales DIS Design Services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_CVA6_CNTXT_SV__
`define __UVME_CVA6_CNTXT_SV__

/**
 * Object encapsulating all state variables for CVA6 environment
 * (uvme_cva6_env_c) components.
 */
class uvme_cva6_cntxt_c extends uvm_object;

   // Agent context handles
   uvma_clknrst_cntxt_c    clknrst_cntxt;

   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;


   `uvm_object_utils_begin(uvme_cva6_cntxt_c)
      `uvm_field_object(clknrst_cntxt,   UVM_DEFAULT)
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end


   /**
    * Builds events and sub-context objects.
    */
   extern function new(string name="uvme_cva6_cntxt");

endclass : uvme_cva6_cntxt_c


function uvme_cva6_cntxt_c::new(string name="uvme_cva6_cntxt");

   super.new(name);

   clknrst_cntxt   = uvma_clknrst_cntxt_c::type_id::create("clknrst_cntxt");

   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");

endfunction : new

`endif // __UVME_CVA6_CNTXT_SV__
