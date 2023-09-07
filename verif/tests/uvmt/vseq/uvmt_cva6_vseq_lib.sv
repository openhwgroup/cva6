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


`ifndef __UVMT_CVA6_VSEQ_LIB_SV__
`define __UVMT_CVA6_VSEQ_LIB_SV__


/**
 * Object holding virtual sequence library for CVA6 test cases.
 */
class uvmt_cva6_vseq_lib_c extends uvm_sequence_library#(
   .REQ(uvm_sequence_item),
   .RSP(uvm_sequence_item)
);

   `uvm_object_utils          (uvmt_cva6_vseq_lib_c)
   `uvm_sequence_library_utils(uvmt_cva6_vseq_lib_c)


   /**
    * Initializes sequence library.
    */
   extern function new(string name="uvmt_cva6_vseq_lib");

endclass : uvmt_cva6_vseq_lib_c


function uvmt_cva6_vseq_lib_c::new(string name="uvmt_cva6_vseq_lib");

   super.new(name);
   init_sequence_library();

   // TODO Add sequences to uvmt_cva6_vseq_lib_c
   //      Ex: add_sequence(uvmt_cva6_abc_vseq_c::get_type());

endfunction : new


`endif // __UVMT_CVA6_VSEQ_LIB_SV__
