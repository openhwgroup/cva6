//
// Copyright 2020 OpenHW Group
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
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//
// riscv_rvalid_stall.sv
//
// Simple FIFO to store data responses for the OBI
// This file should be completely compatible with Verilator and all commerical SystemVerilog simulators
//
// Author: Steve Richmond
//   email: steve.richmond@silabs.com
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

module riscv_rvalid_stall(
    // Clock, reset
    input               clk_i,
    input               rst_ni,

    // Request/gnt interface, to push entries into the FIFO
    input               req_i,
    input               gnt_i,
    input               we_i,

    // Read data valid, signals that read data from RAM is valid on this cycle
    input [31:0]        rdata_i,

    // Response bus, connect directly to OBI response port
    output logic [31:0] rdata_o,
    output logic        rvalid_o,

    // Stall knobs
    input logic         en_stall_i,
    input logic [31:0]  stall_mode_i,
    input logic [31:0]  max_stall_i,
    input logic [31:0]  valid_stall_i
);

// -----------------------------------------------------------------------------------------------
// Local parameters
// -----------------------------------------------------------------------------------------------
localparam FIFO_DATA_WL  = 32;
localparam FIFO_DELAY_WL = 4; // Up to 15 cycles of delay
localparam FIFO_WE_WL    = 1;

localparam FIFO_DATA_LSB  = 0;
localparam FIFO_DELAY_LSB = FIFO_DATA_LSB + FIFO_DATA_WL;
localparam FIFO_WE_LSB    = FIFO_DELAY_LSB + FIFO_DELAY_WL;

localparam FIFO_WL = FIFO_DATA_WL + FIFO_DELAY_WL + FIFO_WE_WL;

localparam FIFO_DEPTH = 8;
localparam FIFO_PTR_WL = $clog2(FIFO_DEPTH) + 1;

// -----------------------------------------------------------------------------------------------
// Local variables
// -----------------------------------------------------------------------------------------------
wire fifo_empty;
wire fifo_full;
wire fifo_push;

logic [FIFO_PTR_WL-1:0] wptr;
logic [FIFO_PTR_WL-1:0] rptr;
logic [FIFO_PTR_WL-2:0] wptr_rdata;

reg [FIFO_WL-1:0] fifo[FIFO_DEPTH];
reg rvalid_i_q;

wire [FIFO_DELAY_WL-1:0] current_delay;

integer i;

// -----------------------------------------------------------------------------------------------
// Tasks and functions
// -----------------------------------------------------------------------------------------------
`ifndef VERILATOR
function logic [FIFO_DELAY_WL-1:0] get_random_delay();
    if (!en_stall_i)
        get_random_delay = 0;
    else if (stall_mode_i == perturbation_defines::STANDARD)
        get_random_delay = valid_stall_i;
    else if (stall_mode_i == perturbation_defines::RANDOM)
        get_random_delay = $urandom_range(max_stall_i, 0);
    else
        get_random_delay = 0;
endfunction : get_random_delay
`endif

// -----------------------------------------------------------------------------------------------
// Begin module code
// -----------------------------------------------------------------------------------------------

assign fifo_push = req_i && gnt_i;

always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        wptr <= '0;
        rptr <= '0;
    end
    else begin
        wptr <= (req_i && gnt_i) ? wptr + 1 : wptr;
        rptr <= (rvalid_o) ? rptr + 1 : rptr;
    end
end

assign fifo_empty = (wptr == rptr) ? 1 : 0;
assign fifo_full  = (wptr == {~rptr[FIFO_PTR_WL-1], rptr[FIFO_PTR_WL-2:0]}) ? 1 : 0;

always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
        for (i = 0; i < FIFO_DEPTH; i++) begin
            fifo[i] = {FIFO_WL{1'b0}};
        end
    end
    else begin
        if (fifo_push) begin
            fifo[wptr[FIFO_PTR_WL-2:0]] = {
                we_i,
`ifdef VERILATOR
                4'h0,
`else
                get_random_delay(),
`endif
                32'h0};

            wptr_rdata <= wptr[FIFO_PTR_WL-2:0];

            rvalid_i_q <= (!we_i) ? 1 : 0;
        end
        else begin
            rvalid_i_q <= 1'b0;
        end

        if (rvalid_i_q) begin
            fifo[wptr_rdata][31:0] <= fifo[wptr_rdata][FIFO_WE_LSB] ? 32'h0 : rdata_i;
        end
    end
end

// Read interface
assign current_delay = fifo[rptr[FIFO_PTR_WL-2:0]][FIFO_DELAY_LSB +: FIFO_DELAY_WL];

always @(*) begin
    rdata_o = '0;
    rvalid_o = '0;
    if (!fifo_empty && current_delay == 0) begin
        rvalid_o = 1'b1;
        if (rptr[FIFO_PTR_WL-2:0] == wptr_rdata && rvalid_i_q)
            if (fifo[rptr[FIFO_PTR_WL-2:0]][FIFO_WE_LSB])
                rdata_o = 32'h0;
            else
                rdata_o = rdata_i;
        else
            rdata_o = fifo[rptr[FIFO_PTR_WL-2:0]][FIFO_DATA_LSB +: FIFO_DATA_WL];
    end
end

// Manage current delay counter
always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
    end
    else begin
        if (!fifo_empty && current_delay > 0) begin
            fifo[rptr[FIFO_PTR_WL-2:0]][FIFO_DELAY_LSB +: FIFO_DELAY_WL] <= current_delay - 1;
        end
    end
end

endmodule : riscv_rvalid_stall
