// Author: Florian Zaruba, ETH Zurich
// Date: 14.05.2017
// Description: Dual Port fetch FIFO with instruction aligner and support for compressed instructions
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//

import ariane_pkg::*;

module fetch_fifo
(
    input  logic                   clk_i,
    input  logic                   rst_ni,
    // control signals
    input  logic                   flush_i,    // clears the contents of the FIFO -> quasi reset
    // branch prediction at in_addr_i address, as this is an address and not PC it can be the case
    // that we have two compressed instruction (or one compressed instruction and one unaligned instruction) so we
    // only predict on one entry and discard (or keep) the other depending on its position and prediction.
    // input port
    input  branchpredict_sbe       branch_predict_i,
    input  exception               ex_i,              // fetch exception in
    input  logic [63:0]            in_addr_i,
    input  logic [63:0]            in_rdata_i,
    input  logic                   in_valid_i,
    output logic                   in_ready_o,
    // Dual Port Fetch FIFO
    // output port 0
    output fetch_entry             fetch_entry_0_o,
    output logic                   fetch_entry_valid_0_o,
    input  logic                   fetch_ack_0_i,
    // output port 1
    output fetch_entry             fetch_entry_1_o,
    output logic                   fetch_entry_valid_1_o,
    input  logic                   fetch_ack_1_i
);

    localparam int unsigned DEPTH = 4; // must be a power of two
    // status signals
    logic full, empty;

    fetch_entry                   mem_n[DEPTH-1:0], mem_q[DEPTH-1:0];
    logic [$clog2(DEPTH)-1:0]     read_pointer_n,   read_pointer_q;
    logic [$clog2(DEPTH)-1:0]     write_pointer_n,  write_pointer_q;
    logic [$clog2(DEPTH)-1:0]     status_cnt_n,     status_cnt_q; // this integer will be truncated by the synthesis tool

    assign in_ready_o = (status_cnt_q < DEPTH-2);
    assign full = (status_cnt_q == DEPTH);
    assign empty = (status_cnt_q == '0);

    // -------------
    // Downsize
    // -------------
    logic [31:0] in_rdata;
    // downsize from 64 bit to 32 bit, simply ignore half of the incoming data
    always_comb begin : downsize
        // take the upper half
        if (in_addr_i[2])
            in_rdata = in_rdata_i[63:32];
        // take the lower half of the instruction
        else
            in_rdata = in_rdata_i[31:0];
    end

    always_comb begin : fetch_fifo_logic
        // counter
        automatic logic [$clog2(DEPTH)-1:0] status_cnt    = status_cnt_q;
        automatic logic [$clog2(DEPTH)-1:0] write_pointer = write_pointer_q;
        automatic logic [$clog2(DEPTH)-1:0] read_pointer  = read_pointer_q;

        mem_n = mem_q;

        // -------------
        // Input Port
        // -------------
        if (in_valid_i) begin
            status_cnt++;
            // new input data
            mem_n[write_pointer_q] = {in_addr_i, in_rdata, branch_predict_i, ex_i};
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
    assert property (@(posedge clk_i) (in_valid_i |-> !full)) else $error("Got a valid signal, although the queue is not ready to accept a new request");
    `endif
    `endif
endmodule