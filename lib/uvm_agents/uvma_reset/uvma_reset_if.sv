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


`ifndef __UVMA_RESET_IF_SV__
`define __UVMA_RESET_IF_SV__


/**
 * Encapsulates all signals and clocking of Reset interface. Used by
 * monitor and driver.
 */
interface uvma_reset_if(
   input  clk  ,
   input  reset
);
   
   // TODO Add uvma_reset_if signals
   // Ex:  wire        enable;
   //      wire [7:0]  data;
   
   
   /**
    * Used by target DUT.
    */
   clocking dut_cb @(posedge clk or reset);
      // TODO Implement uvma_reset_if::dut_cb()
      //      Ex: input  enable,
      //                 data  ;
   endclocking : dut_cb
   
   /**
    * Used by uvma_reset_drv_c.
    */
   clocking drv_cb @(posedge clk or reset);
      // TODO Implement uvma_reset_if::drv_cb()
      //      Ex: output  enable,
      //                  data  ;
   endclocking : drv_cb
   
   /**
    * Used by uvma_reset_mon_c.
    */
   clocking mon_cb @(posedge clk or reset);
      // TODO Implement uvma_reset_if::mon_cb()
      //      Ex: input  enable,
      //                 data  ;
   endclocking : mon_cb
   
   
   modport dut_mp    (clocking dut_cb);
   modport active_mp (clocking drv_cb);
   modport passive_mp(clocking mon_cb);
   
endinterface : uvma_reset_if


`endif // __UVMA_RESET_IF_SV__
