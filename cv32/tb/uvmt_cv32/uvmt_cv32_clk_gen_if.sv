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

`ifndef __UVMT_CV32_CLK_GEN_IF_SV__
`define __UVMT_CV32_CLK_GEN_IF_SV__


/**
 * Interface providing clock signals to all other interfaces used by CV32
 * test bench (uvmt_cv32_tb). Managed by test cases.
 */
interface uvmt_cv32_clk_gen_if;
   
   bit       start_clk = 0;
   logic     reset_clk        = 0;
   realtime  reset_clk_period = uvme_cv32_reset_default_clk_period * 1ps;
   logic     debug_clk        = 0;
   realtime  debug_clk_period = uvme_cv32_debug_default_clk_period * 1ps;
   
   
   /**
    * Generates clock signals.
    */
   initial begin
      wait (start_clk);
      fork
         forever begin
            #(reset_clk_period/2) reset_clk = ~reset_clk;
         end
         forever begin
            #(debug_clk_period/2) debug_clk = ~debug_clk;
         end
      join_none
   end
   
   /**
    * Sets clock period in ps.
    */
   function void set_clk_periods(
      real reset_period,
      real debug_period
   );
      reset_clk_period = reset_period * 1ps;
      debug_clk_period = debug_period * 1ps;
   endfunction : set_clk_period
   
   /**
    * Triggers the generation of clk.
    */
   function void start();
      start_clk = 1;
   endfunction : start
   
endinterface : uvmt_cv32_clk_gen_if


`endif // __UVMT_CV32_CLK_GEN_IF_SV__
