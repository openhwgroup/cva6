// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 15/07/2017
// Description: A RISC-V privilege spec 1.11 (WIP) compatible timer
//

// Platforms provide a real-time counter, exposed as a memory-mapped machine-mode register, mtime. mtime must run at
// constant frequency, and the platform must provide a mechanism for determining the timebase of mtime.

module ariane_timer #(
    parameter int unsigned AXI_ADDR_WIDTH = 64,
    parameter int unsigned AXI_DATA_WIDTH = 64,
    parameter int unsigned AXI_ID_WIDTH   = 10,
    parameter int unsigned NR_CORES        = 1 // Number of cores therefore also the number of timecmp registers and timer interrupts
)(
    // APB Slave
    input  logic           clk_i,   // Clock
    input  logic           rst_ni,  // Asynchronous reset active low

    AXI_BUS.Slave          slave,

    input  logic           halted_i, // cores are halted, also halt timer
    input  logic           rtc_i,    // Real-time clock in (usually 32.768 kHz)
    output logic    [63:0] time_o,   // Global Time out, this is the time-base of the whole SoC
    output logic           irq_o     // Timer interrupt
);
    // register offset
    localparam logic [1:0] REG_CMP  = 2'h1;
    localparam logic [1:0] REG_TIME = 2'h3;
    // signals from AXI 4 Lite
    logic [AXI_ADDR_WIDTH-1:0] address;
    logic                      en;
    logic                      we;
    logic [63:0] wdata;
    logic [63:0] rdata;

    // bit 11 and 10 are determining the address offset
    logic [1:0] register_address;
    assign register_address = address[11:10];
    // actual registers
    logic [63:0]               mtime_n, mtime_q;
    logic [NR_CORES-1:0][63:0] mtimecmp_n, mtimecmp_q;

    // increase the timer
    logic increase_timer;

    // directly output the mtime_q register - this needs synchronization (but in the core).
    assign time_o = mtime_q;

    // -----------------------------
    // AXI Interface Logic
    // -----------------------------
    axi_lite_interface #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH    )
    ) axi_lite_interface_i (
        .address_o ( address ),
        .en_o      ( en      ),
        .we_o      ( we      ),
        .data_i    ( rdata   ),
        .data_o    ( wdata   ),
        .*
    );

    // -----------------------------
    // Register Update Logic
    // -----------------------------
    // APB register write logic
    always_comb begin
        mtime_n    = mtime_q;
        mtimecmp_n = mtimecmp_q;

        // RTC says we should increase the timer
        if (increase_timer && !halted_i)
            mtime_n = mtime_q + 1;

        // written from APB bus - gets priority
        if (en && we) begin
            case (register_address)
                REG_TIME:
                    mtime_n = wdata;

                REG_CMP:
                    mtimecmp_n[$unsigned(address[NR_CORES-1+3:3])] = wdata;
                default:;
            endcase
        end
    end

    // APB register read logic
    always_comb begin
        rdata = 'b0;

        if (en && !we) begin
            case (register_address)
                REG_TIME:
                    rdata = mtime_q;

                REG_CMP:
                    rdata = mtimecmp_q[$unsigned(address[NR_CORES-1+3:3])];
                default:;
            endcase
        end
    end

    // -----------------------------
    // IRQ Generation
    // -----------------------------
    // The mtime register has a 64-bit precision on all RV32, RV64, and RV128 systems. Platforms provide a 64-bit
    // memory-mapped machine-mode timer compare register (mtimecmp), which causes a timer interrupt to be posted when the
    // mtime register contains a value greater than or equal (mtime >= mtimecmp) to the value in the mtimecmp register.
    // The interrupt remains posted until it is cleared by writing the mtimecmp register. The interrupt will only be taken
    // if interrupts are enabled and the MTIE bit is set in the mie register.
    always_comb begin : irq_gen
        // check that the mtime cmp register is set to a meaningful value
        if (mtimecmp_q != 0 && mtime_q >= mtimecmp_q)
            irq_o = 1'b1;
        else
            irq_o = 1'b0;
    end

    // -----------------------------
    // RTC time tracking facilities
    // -----------------------------
    // 1. Put the RTC input through a classic two stage edge-triggered synchronizer to filter out any
    //    metastability effects (or at least make them unlikely :-))
    sync_wedge i_sync_edge (
        .en_i      ( 1'b1           ),
        .serial_i  ( rtc_i          ),
        .r_edge_o  ( increase_timer ),
        .f_edge_o  (                ), // left open
        .serial_o  (                ),
        .*
    );

    // Registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            mtime_q    <= 64'b0;
            mtimecmp_q <= 'b0;
        end else begin
            mtime_q    <= mtime_n;
            mtimecmp_q <= mtimecmp_n;
        end
    end

    // -------------
    // Assertions
    // --------------
    `ifndef SYNTHESIS
    `ifndef VERILATOR
    // Static assertion check for appropriate bus width
        initial begin
            assert (AXI_DATA_WIDTH == 64) else $fatal("Timer needs to interface with a 64 bit bus, everything else is not supported");
        end
    `endif
    `endif
endmodule
