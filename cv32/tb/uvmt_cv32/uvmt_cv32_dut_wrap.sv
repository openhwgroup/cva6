//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
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


`ifndef __UVMT_CV32_DUT_WRAP_SV__
`define __UVMT_CV32_DUT_WRAP_SV__


/**
 * Module wrapper for CV32 RTL DUT. All ports are SV interfaces.
 */
module uvmt_cv32_dut_wrap(
   uvma_debug_if  debug_if
);
   
   // TODO Instantiate Device Under Test (DUT)
   //      Ex: cv32_top  dut(
   //             .debug_data(debug_if.data),
   //             ...
   //          );
   
endmodule : uvmt_cv32_dut_wrap


`endif // __UVMT_CV32_DUT_WRAP_SV__
