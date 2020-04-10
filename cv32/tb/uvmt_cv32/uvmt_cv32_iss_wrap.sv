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
 */
module uvmt_cv32_iss_wrap
  #(
    parameter ID         = 0,
              VENDOR     = "riscv.ovpworld.org",
              VARIANT    = "RV32GC",
              COMPARE    = 0,
              STOPONTRAP = 1
   )

   (
   // uvma_clknrst_if  clknrst_if
   ); // module uvmt_cv32_iss_wrap

  //import uvm_pkg::*; // needed for the UVM messaging service (`uvm_info(), etc.)

  BUS  b1();
  RAM  ram(b1);
  INTC intc(b1);
//
  MONITOR
     #(
       .ID         (ID),
       .VARIANT    (VARIANT),
       .STOPONTRAP (STOPONTRAP)
      )
       mon(b1);
//
  CPU
     #(
       .ID      (ID), 
       .VENDOR  (VENDOR), 
       .VARIANT (VARIANT),
       .COMPARE (COMPARE)
      )
       cpu(b1);

  reg Clk;
  assign Clk = b1.Clk;
    
  reg [31:0] Addr;
  assign Addr = b1.Addr;

  reg [31:0] Data;
  assign Data = b1.Data;
    
  reg [2:0] Size;
  assign Size = b1.Size;

  reg [1:0] Transfer;
  assign Transfer = b1.Transfer;
    
  reg Load, Store, Fetch;
    
  always @Transfer begin
    Load  = (Transfer == 1) ? 1 : 0;
    Store = (Transfer == 2) ? 1 : 0;
    Fetch = (Transfer == 3) ? 1 : 0;
  end
   
  //assign b1.Clk = clknrst_if.clk;

  initial begin
    b1.Clk = 0;
    forever begin
      #10 b1.Clk <= ~b1.Clk;
    end
  end

endmodule : uvmt_cv32_iss_wrap

`endif // __UVMT_CV32_ISS_WRAP_SV__

