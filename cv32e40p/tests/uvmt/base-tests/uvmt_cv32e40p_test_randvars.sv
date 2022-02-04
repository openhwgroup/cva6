// Copyright 2021 OpenHW Group
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

// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

`ifndef __UVMT_CV32E40P_TEST_RANDVARS_SV__
`define __UVMT_CV32E40P_TEST_RANDVARS_SV__


/**
 * Object of randomizable variables
 */
class uvmt_cv32e40p_test_randvars_c extends uvm_object;

   rand int unsigned  random_int;
   rand logic [31:0]  random_logic32;
   rand logic         random_logic_bit;

   `uvm_object_utils_begin(uvmt_cv32e40p_test_randvars_c)
      `uvm_field_int(random_int,       UVM_DEFAULT)
      `uvm_field_int(random_logic32,   UVM_DEFAULT)
      `uvm_field_int(random_logic_bit, UVM_DEFAULT)
   `uvm_object_utils_end


   extern function new(string name="uvmt_cv32e40p_test_randvars");

endclass : uvmt_cv32e40p_test_randvars_c


function uvmt_cv32e40p_test_randvars_c::new(string name="uvmt_cv32e40p_test_randvars");

   super.new(name);

endfunction : new


`endif // __UVMT_CV32E40P_TEST_RANDVARS_SV__
