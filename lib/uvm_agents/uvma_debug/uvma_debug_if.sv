// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_DEBUG_IF_SV__
`define __UVMA_DEBUG_IF_SV__


/**
 * Encapsulates all signals and clocking of Debug interface. Used by
 * monitor and driver.
 */
interface uvma_debug_if(
);
    wire clk;
    wire reset_n;
    wire debug_req;
  
    bit is_active; 
    bit debug_drv;

    assign debug_req = is_active ? debug_drv : 1'b0;

    initial begin
        is_active = 1'b0;
        debug_drv = 1'b0;
    end
   /**
    * Used by target DUT.
    */

   clocking dut_cb @(posedge clk or reset_n);
   endclocking : dut_cb
   
   /**
    * Used by uvma_debug_drv_c.
    */
   clocking drv_cb @(posedge clk or reset_n);
      // TODO Implement uvma_debug_if::drv_cb()
      //      Ex: output  enable,
      //                  data  ;
       output debug_drv;
   endclocking : drv_cb
   
   /**
    * Used by uvma_debug_mon_c.
    */
   clocking mon_cb @(posedge clk or reset_n);
       input #1step debug_drv;
   endclocking : mon_cb
   
   
   modport dut_mp    (clocking dut_cb);
   modport active_mp (clocking drv_cb);
   modport passive_mp(clocking mon_cb);
   
endinterface : uvma_debug_if


`endif // __UVMA_DEBUG_IF_SV__
