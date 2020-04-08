// 
// Copyright 2020 OpenHW Group
// 
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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


`ifndef __OVPM_ENCAP_PKG_SV__
`define __OVPM_ENCAP_PKG_SV__

/**
 * Package file for the Imperas ISS "OVPmodel encapsulation" example.
 */

// Pre-processor macros
`include "uvm_macros.svh"


`include "verilog_OVPmodel/typedefs.sv"
`include "verilog_OVPmodel/interface.sv"
`include "verilog_OVPmodel/monitor.sv"
`include "verilog_OVPmodel/cpu.sv"

`include "verilog_model/intc.sv"
`include "verilog_model/ram.sv"

//`include "verilog_testbench/verilog_testbench_dut.sv"  // replaced by uvmt_cv32_iss_wrap
`include "verilog_testbench/testbench.sv"
`include "verilog_testbench/class_simple_coverage.svh"
   
package ovpm_encap_pkg;
   
   import uvm_pkg::*;

endpackage : ovpm_encap_pkg


`endif // __OVPM_ENCAP_PKG_SV__
