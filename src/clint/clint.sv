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
// Description: A RISC-V privilege spec 1.11 (WIP) compatible CLINT (core local interrupt controller)
//

// Platforms provide a real-time counter, exposed as a memory-mapped machine-mode register, mtime. mtime must run at
// constant frequency, and the platform must provide a mechanism for determining the timebase of mtime (device tree).

module clint #(
    parameter int unsigned AXI_ADDR_WIDTH = 64,
    parameter int unsigned AXI_DATA_WIDTH = 64,
    parameter int unsigned AXI_ID_WIDTH   = 10,
    parameter int unsigned NR_CORES       = 1 // Number of cores therefore also the number of timecmp registers and timer interrupts
) (
    input  logic                clk_i,       // Clock
    input  logic                rst_ni,      // Asynchronous reset active low
    input  logic                testmode_i,
    input  ariane_axi::req_t    axi_req_i,
    output ariane_axi::resp_t   axi_resp_o,
    input  logic                rtc_i,       // Real-time clock in (usually 32.768 kHz)
    output logic [NR_CORES-1:0] timer_irq_o, // Timer interrupts
    output logic [NR_CORES-1:0] ipi_o        // software interrupt (a.k.a inter-process-interrupt)
);
    // register offset
    localparam logic [15:0] MSIP_BASE     = 16'h0;
    localparam logic [15:0] MTIMECMP_BASE = 16'h4000;
    localparam logic [15:0] MTIME_BASE    = 16'hbff8;

    localparam AddrSelWidth = (NR_CORES == 1) ? 1 : $clog2(NR_CORES);

    // signals from AXI 4 Lite
    logic [AXI_ADDR_WIDTH-1:0] address;
    logic                      en;
    logic                      we;
    logic [63:0] wdata;
    logic [63:0] rdata;

    // bit 11 and 10 are determining the address offset
    logic [15:0] register_address;
    assign register_address = address[15:0];
    // actual registers
    logic [63:0]               mtime_n, mtime_q;
    logic [NR_CORES-1:0][63:0] mtimecmp_n, mtimecmp_q;
    logic [NR_CORES-1:0]       msip_n, msip_q;
    // increase the timer
    logic increase_timer;

    // -----------------------------
    // AXI Interface Logic
    // -----------------------------
    axi_lite_interface #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH    )
    ) axi_lite_interface_i (
        .clk_i      ( clk_i      ),
        .rst_ni     ( rst_ni     ),
        .axi_req_i  ( axi_req_i  ),
        .axi_resp_o ( axi_resp_o ),
        .address_o  ( address    ),
        .en_o       ( en         ),
        .we_o       ( we         ),
        .data_i     ( rdata      ),
        .data_o     ( wdata      )
    );

    // -----------------------------
    // Register Update Logic
    // -----------------------------
    // APB register write logic
    always_comb begin
        mtime_n    = mtime_q;
        mtimecmp_n = mtimecmp_q;
        msip_n     = msip_q;
        // RTC says we should increase the timer
        if (increase_timer)
            mtime_n = mtime_q + 1;

        // written from APB bus - gets priority
        if (en && we) begin
            case (register_address) inside
                [MSIP_BASE:MSIP_BASE+8*NR_CORES]: begin
                    msip_n[$unsigned(address[AddrSelWidth-1+3:3])] = wdata[0];
                end

                [MTIMECMP_BASE:MTIMECMP_BASE+8*NR_CORES]: begin
                    mtimecmp_n[$unsigned(address[AddrSelWidth-1+3:3])] = wdata;
                end

                MTIME_BASE: begin
                    mtime_n = wdata;
                end
                default:;
            endcase
        end
    end

    // APB register read logic
    always_comb begin
        rdata = 'b0;

        if (en && !we) begin
            case (register_address) inside
                [MSIP_BASE:MSIP_BASE+8*NR_CORES]: begin
                    rdata = msip_q[$unsigned(address[AddrSelWidth-1+3:3])];
                end

                [MTIMECMP_BASE:MTIMECMP_BASE+8*NR_CORES]: begin
                    rdata = mtimecmp_q[$unsigned(address[AddrSelWidth-1+3:3])];
                end

                MTIME_BASE: begin
                    rdata = mtime_q;
                end
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
        for (int unsigned i = 0; i < NR_CORES; i++) begin
            if (mtime_q >= mtimecmp_q[i]) begin
                timer_irq_o[i] = 1'b1;
            end else begin
                timer_irq_o[i] = 1'b0;
            end
        end
    end

    // -----------------------------
    // RTC time tracking facilities
    // -----------------------------
    // 1. Put the RTC input through a classic two stage edge-triggered synchronizer to filter out any
    //    metastability effects (or at least make them unlikely :-))
    sync_wedge i_sync_edge (
        .clk_i,
        .rst_ni,
        .en_i      ( ~testmode_i    ),
        .serial_i  ( rtc_i          ),
        .r_edge_o  ( increase_timer ),
        .f_edge_o  (                ), // left open
        .serial_o  (                )  // left open
    );

    // Registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            mtime_q    <= 64'b0;
            mtimecmp_q <= 'b0;
            msip_q     <= '0;
        end else begin
            mtime_q    <= mtime_n;
            mtimecmp_q <= mtimecmp_n;
            msip_q     <= msip_n;
        end
    end

    assign ipi_o = msip_q;

    // -------------
    // Assertions
    // --------------
    //pragma translate_off
    `ifndef VERILATOR
    // Static assertion check for appropriate bus width
        initial begin
            assert (AXI_DATA_WIDTH == 64) else $fatal("Timer needs to interface with a 64 bit bus, everything else is not supported");
        end
    `endif
    //pragma translate_on

endmodule
