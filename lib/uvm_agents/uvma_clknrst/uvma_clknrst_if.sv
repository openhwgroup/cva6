// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_CLKNRST_IF_SV__
`define __UVMA_CLKNRST_IF_SV__


/**
 * Encapsulates all signals of the Clock & Reset interface. Used by monitor 
 * (uvma_clknrst_mon_c) and driver (uvma_clknrst_drv_c).
 */
interface uvma_clknrst_if ();

   import uvm_pkg::*;
   
   // Signals
   logic  clk    ;
   logic  reset_n;
   
   // Control fields
   realtime  clk_period    ;
   bit       clk_active = 0;
   
   
   /**
    * Clock generation loop
    */
   initial begin
      wait (clk_active);
      forever begin
         #(clk_period);
         if (clk_active) begin
            case (clk)
               '0: clk = 1; // 0 -> 1
               '1: clk = 0; // 1 -> 0
               'X: clk = 0; // X -> 0
            endcase
         end
      end
   end
   
   always @* begin
      if (clk_active && clk_period == 0.0) 
         `uvm_fatal("CLKNRSTIF", $sformatf("%m: Clock is active with 0 period"))
   end
   /**
    * Sets clk_period
    */
   function void set_period(realtime new_clk_period);
      `uvm_info("CLKNRST", $sformatf("Changing clock period to %0t", new_clk_period), UVM_LOW)
      clk_period = new_clk_period;
   endfunction : set_period
   
   /**
    * Sets clk_active to 1
    */
   function void start_clk();
      `uvm_info("CLKNRST", "Starting clock generation", UVM_HIGH)
      if (clk_period) clk_active = 1;
   endfunction : start_clk
   
   /**
    * Sets clk_active to 0
    */
   function void stop_clk();
      `uvm_info("CLKNRST", "Stopping clock generation", UVM_HIGH)
      clk_active = 0;
   endfunction : stop_clk
   
endinterface : uvma_clknrst_if


`endif // __UVMA_CLKNRST_IF_SV__
