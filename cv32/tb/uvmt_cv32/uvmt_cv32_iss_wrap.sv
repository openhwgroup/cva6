//
// Copyright 2020 OpenHW Group
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
//


`ifndef __UVMT_CV32_ISS_WRAP_SV__
`define __UVMT_CV32_ISS_WRAP_SV__


/**
 * Module wrapper for Imperas ISS.
 * Instanitates "CPU", the ISS wrapper, and "RAM" a spare memory model.
 */
module uvmt_cv32_iss_wrap
  #(
    //parameter int ROM_START_ADDR = 'h8000,
    //parameter int ROM_BYTE_SIZE  = 'h20000,
    //parameter int RAM_BYTE_SIZE  = 'h20000,
    parameter int ROM_START_ADDR = 'h00000000,
    parameter int ROM_BYTE_SIZE  = 'h0,
    parameter int RAM_BYTE_SIZE  = 'h400000,
    parameter int ID = 0
   )

   (
    input wire clk_i
   );

  //import uvm_pkg::*; // needed for the UVM messaging service (`uvm_info(), etc.)

    BUS         b1();
    
    MONITOR     mon(b1);
    RAM         #(
                .ROM_START_ADDR(ROM_START_ADDR),
                .ROM_BYTE_SIZE(ROM_BYTE_SIZE),
                .RAM_BYTE_SIZE(RAM_BYTE_SIZE)) ram(b1);
   
    CPU #(.ID(ID)) cpu(b1);

  assign b1.Clk = clk_i;

endmodule : uvmt_cv32_iss_wrap

`endif // __UVMT_CV32_ISS_WRAP_SV__

