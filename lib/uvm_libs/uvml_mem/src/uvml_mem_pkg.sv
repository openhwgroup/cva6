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


`ifndef __UVML_MEM_PKG_SV__
`define __UVML_MEM_PKG_SV__


// Pre-processor macros
`include "uvm_macros.svh"
`include "uvml_mem_macros.sv"


/**
 * Encapsulates all the types needed for Memory base class library.
 */
package uvml_mem_pkg;
   
   import uvm_pkg::*;
   
   // Constants / Structs / Enums
   `include "uvml_mem_tdefs.sv"
   `include "uvml_mem_constants.sv"
  
   // Objects
   `include "uvml_mem_model.sv"
   
endpackage : uvml_mem_pkg


`endif // __UVML_MEM_PKG_SV__
