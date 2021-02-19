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


`ifndef __UVMA_INTERRUPT_IF_SV__
`define __UVMA_INTERRUPT_IF_SV__


/**
 * Encapsulates all signals and clocking of Interrupt interface. Used by
 * monitor and driver.
 */
interface uvma_interrupt_if
   (
   );

    // ---------------------------------------------------------------------------
    // Interface wires
    // ---------------------------------------------------------------------------
    wire        clk;
    wire        reset_n;
    wire [31:0] irq;
    wire        irq_ack;
    wire [4:0]  irq_id;

    // Used to time true interrupt entry with tracer instruction retirement
    wire        deferint;
    wire        ovp_cpu_state_stepi;

    // -------------------------------------------------------------------
    // Testbench control
    // ---------------------------------------------------------------------------
    // -------------------------------------------------------------------
    bit         is_active;  // Set to active drive the interrupt lines
    bit [31:0]  irq_drv;       // TB interrupt driver

    // -------------------------------------------------------------------
    // Begin module code
    // -------------------------------------------------------------------

    // Mux in driver to irq lines
    assign irq = is_active ? irq_drv : 1'b0;

    initial begin
        is_active = 1'b0;
        irq_drv = '0;
    end

   
    /**
        * Used by target DUT.
    */
    clocking dut_cb @(posedge clk or reset_n);
    endclocking : dut_cb
    
    /**
       * Used by uvma_interrupt_drv_c.
    */
    clocking drv_cb @(posedge clk or reset_n);
        input #1step irq_ack, 
                     irq_id;
        output       irq_drv;
    endclocking : drv_cb
   
    /**
        * Used by uvma_interrupt_mon_c.
    */
    clocking mon_cb @(posedge clk or reset_n);
        input #1step irq_ack, 
                     irq_id,
                     irq_drv;
    endclocking : mon_cb
      
    modport dut_mp    (clocking dut_cb);
    modport active_mp (clocking drv_cb);
    modport passive_mp(clocking mon_cb);

endinterface : uvma_interrupt_if


`endif // __UVMA_INTERRUPT_IF_SV__
