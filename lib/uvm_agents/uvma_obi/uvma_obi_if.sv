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


`ifndef __UVMA_OBI_IF_SV__
`define __UVMA_OBI_IF_SV__


/**
 * Encapsulates all signals and clocking of Obi interface. Used by
 * monitor and driver.
 */
interface uvma_obi_if
   (
       input clk,
       input reset_n,
       input req,
       input gnt,
       input [31:0] addr,
       input we,
       input [3:0] be,    
       input [31:0] wdata,
       input [31:0] rdata,
       input rvalid,
       input rready
   );

    // -------------------------------------------------------------------
    // Testbench control
    // ---------------------------------------------------------------------------
    // -------------------------------------------------------------------
    bit         is_active;  // Set to active drive the obi lines

    // -------------------------------------------------------------------
    // Begin module code
    // -------------------------------------------------------------------

    initial begin
        is_active = 1'b0;
    end

   
    /**
        * Used by target DUT.
    */
    clocking dut_cb @(posedge clk or reset_n);
    endclocking : dut_cb
    
    /**
       * Used by uvma_obi_drv_c.
    */
    clocking drv_mst_cb @(posedge clk or reset_n);
        input #1step gnt,
                     rvalid,
                     rdata;                     
        output       req,
                     we,
                     addr,
                     be,
                     wdata,
                     rready;
    endclocking : drv_mst_cb

    /**
       * Used by uvma_obi_drv_c.
    */
    clocking drv_slv_cb @(posedge clk or reset_n);
        output       gnt,
                     rvalid,
                     rdata;                     
        input #1step req,
                     we,
                     addr,
                     be,
                     wdata,
                     rready;
    endclocking : drv_slv_cb

    /**
        * Used by uvma_obi_mon_c.
    */
    clocking mon_cb @(posedge clk or reset_n);
        input #1step gnt,
                     rvalid,
                     rdata,
                     req,
                     we,
                     addr,
                     be,
                     wdata,
                     rready;
    endclocking : mon_cb

    modport dut_mp        (clocking dut_cb);
    modport active_mst_mp (clocking drv_mst_cb);
    modport active_slv_mp (clocking drv_slv_cb);
    modport passive_mp    (clocking mon_cb);

endinterface : uvma_obi_if


`endif // __UVMA_OBI_IF_SV__
