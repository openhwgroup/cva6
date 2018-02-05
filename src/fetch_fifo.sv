// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 14.05.2017
// Description: Dual Port fetch FIFO with instruction aligner and support for compressed instructions

import ariane_pkg::*;

module fetch_fifo
(
    input  logic                   clk_i,
    input  logic                   rst_ni,
    // control signals
    input  logic                   flush_i,    // clears the contents of the FIFO -> quasi reset
    // branch prediction at addr_i address, as this is an address and not PC it can be the case
    // that we have two compressed instruction (or one compressed instruction and one unaligned instruction) so we
    // only predict on one entry and discard (or keep) the other depending on its position and prediction.
    // input port
    input  branchpredict_sbe_t     branch_predict_i,
    input  exception_t             ex_i,              // fetch exception in
    input  logic [63:0]            addr_i,
    input  logic [63:0]            rdata_i,
    input  logic                   valid_i,
    output logic                   ready_o,
    // Dual Port Fetch FIFO
    // output port 0
    output fetch_entry_t           fetch_entry_0_o,
    output logic                   fetch_entry_valid_0_o,
    input  logic                   fetch_ack_0_i,
    // output port 1
    output fetch_entry_t           fetch_entry_1_o,
    output logic                   fetch_entry_valid_1_o,
    input  logic                   fetch_ack_1_i
);

    localparam int unsigned DEPTH = 4; // must be a power of two
    // status signals
    logic full, empty;

    fetch_entry_t                 mem_n[DEPTH-1:0], mem_q[DEPTH-1:0];
    logic [$clog2(DEPTH)-1:0]     read_pointer_n,   read_pointer_q;
    logic [$clog2(DEPTH)-1:0]     write_pointer_n,  write_pointer_q;
    logic [$clog2(DEPTH)-1:0]     status_cnt_n,     status_cnt_q; // this integer will be truncated by the synthesis tool

    assign ready_o = (status_cnt_q < DEPTH-2);
    assign full = (status_cnt_q == DEPTH);
    assign empty = (status_cnt_q == '0);

    // -------------
    // Downsize
    // -------------
    logic [31:0] in_rdata;
    // downsize from 64 bit to 32 bit, simply ignore half of the incoming data
    always_comb begin : downsize
        // take the upper half
        if (addr_i[2])
            in_rdata = rdata_i[63:32];
        // take the lower half of the instruction
        else
            in_rdata = rdata_i[31:0];
    end

    always_comb begin : fetch_fifo_logic
        // counter
        automatic logic [$clog2(DEPTH)-1:0] status_cnt;
        automatic logic [$clog2(DEPTH)-1:0] write_pointer;
        automatic logic [$clog2(DEPTH)-1:0] read_pointer;
        status_cnt    = status_cnt_q;
        write_pointer = write_pointer_q;
        read_pointer  = read_pointer_q;

        mem_n = mem_q;

        // -------------
        // Input Port
        // -------------
        if (valid_i) begin
            status_cnt++;
            // new input data
            mem_n[write_pointer_q] = {addr_i, in_rdata, branch_predict_i, ex_i};
            write_pointer++;
        end

        // -------------
        // Fetch Port 0
        // -------------
        fetch_entry_valid_0_o = (status_cnt_q >= 1);
        fetch_entry_0_o = mem_q[read_pointer_q];

        if (fetch_ack_0_i) begin
            read_pointer++;
            status_cnt--;
        end

        // -------------
        // Fetch Port 1
        // -------------
        fetch_entry_valid_1_o = (status_cnt_q >= 2);
        fetch_entry_1_o = mem_q[read_pointer_q + 1'b1];

        if (fetch_ack_1_i) begin
            read_pointer++;
            status_cnt--;
        end

        write_pointer_n = write_pointer;
        status_cnt_n    = status_cnt;
        read_pointer_n  = read_pointer;

        if (flush_i) begin
            status_cnt_n    = '0;
            write_pointer_n = 'b0;
            read_pointer_n  = 'b0;
        end

    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            status_cnt_q              <= '{default: 0};
            mem_q                     <= '{default: 0};
            read_pointer_q            <= '{default: 0};
            write_pointer_q           <= '{default: 0};
        end else begin
            status_cnt_q              <= status_cnt_n;
            mem_q                     <= mem_n;
            read_pointer_q            <= read_pointer_n;
            write_pointer_q           <= write_pointer_n;
        end
    end
    //-------------
    // Assertions
    //-------------
    `ifndef SYNTHESIS
    `ifndef VERILATOR
    // Make sure we don't overflow the queue
    assert property (@(posedge clk_i) ((full && !flush_i) |-> ##1 !empty)) else $error("Fetch FIFO Overflowed");
    assert property (@(posedge clk_i) (flush_i || (status_cnt_q - status_cnt_n) <= 2 || (status_cnt_q - status_cnt_n) >= -2)) else $error("Fetch FIFO over- or underflowed");
    assert property (@(posedge clk_i) (valid_i |-> !full)) else $error("Got a valid signal, although the queue is not ready to accept a new request");
    `endif
    `endif
endmodule
