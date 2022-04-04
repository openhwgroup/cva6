//
// Copyright 2020 OpenHW Group
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMT_CV32E40X_UVM_MACROS_INC_SV__
`define __UVMT_CV32E40X_UVM_MACROS_INC_SV__

// Simple inclusion of the uvm_macros.svh file into compilation scope.
// This should only be used in Xcelium where automatic load of UVM does not
// include the macros definition file.
// use of this include file "first" in the simulator compilation filelist
// ensures all macros are properly defined for usage

`include "uvm_macros.svh"

`endif
