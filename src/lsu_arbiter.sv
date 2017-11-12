// Author: Florian Zaruba, ETH Zurich
// Date: 22.05.2017
// Description: Arbitrates the LSU result port
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

import ariane_pkg::*;

module lsu_arbiter (
    input  logic                     clk_i,    // Clock
    input  logic                     rst_ni,   // Asynchronous reset active low
    input  logic                     flush_i,
    // Load Port
    input logic                      ld_valid_i,
    input logic [TRANS_ID_BITS-1:0]  ld_trans_id_i,
    input logic [63:0]               ld_result_i,
    input exception_t                ld_ex_i,
    // Store Port
    input logic                      st_valid_i,
    input logic [TRANS_ID_BITS-1:0]  st_trans_id_i,
    input logic [63:0]               st_result_i,
    input exception_t                st_ex_i,
    // Output Port
    output logic                     valid_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o,
    output exception_t               ex_o
);
    // this is a dual input FIFO which takes results from the load and store
    // paths of the LSU and sequentializes through the FIFO construct. If there is a valid output
    // it unconditionally posts the result on its output ports and expects it to be consumed.

    // 4 entries is enough to unconditionally post loads and stores since we can only have two outstanding loads
    localparam int WIDTH = 4;

    // queue pointer
    logic [$clog2(WIDTH)-1:0] read_pointer_n,  read_pointer_q;
    logic [$clog2(WIDTH)-1:0] write_pointer_n, write_pointer_q;
    logic [$clog2(WIDTH)-1:0] status_cnt_n,    status_cnt_q;

    struct packed {
        logic [TRANS_ID_BITS-1:0] trans_id;
        logic [63:0]              result;
        exception_t               ex;
    } mem_n[WIDTH-1:0], mem_q[WIDTH-1:0];

    // output last element of queue
    assign trans_id_o = mem_q[read_pointer_q].trans_id;
    assign result_o   = mem_q[read_pointer_q].result;
    assign ex_o       = mem_q[read_pointer_q].ex;

    // if we are not empty we have a valid output
    assign valid_o    = (status_cnt_q != '0);
    // -------------------
    // Read-Write Process
    // -------------------
    always_comb begin : read_write_fifo
        automatic logic [$clog2(WIDTH)-1:0] status_cnt;
        automatic logic [$clog2(WIDTH)-1:0] write_pointer;

        status_cnt    = status_cnt_q;
        write_pointer = write_pointer_q;

        // default assignments
        mem_n           = mem_q;
        read_pointer_n  = read_pointer_q;
        // ------------
        // Write Port
        // ------------
        // write port 1 - load unit
        if (ld_valid_i) begin
            mem_n[write_pointer] = {ld_trans_id_i, ld_result_i, ld_ex_i};
            write_pointer++;
            status_cnt++;
        end
        // write port 2 - store unit
        if (st_valid_i) begin
            mem_n[write_pointer] = {st_trans_id_i, st_result_i, st_ex_i};
            write_pointer++;
            status_cnt++;
        end
        // ------------
        // Read Port
        // ------------
        // if the last element in the queue was valid we can push it out and make space for a new element
        if (valid_o) begin
            read_pointer_n = read_pointer_q + 1;
            status_cnt--;
        end

        // update status count
        status_cnt_n    = status_cnt;
        // update write pointer
        write_pointer_n = write_pointer;

        // ------------
        // Flush
        // ------------
        if (flush_i) begin
            status_cnt_n    = '0;
            write_pointer_n = '0;
            read_pointer_n  = '0;
        end
    end
    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            mem_q           <= '{default: 0};
            read_pointer_q  <= '0;
            write_pointer_q <= '0;
            status_cnt_q    <= '0;
        end else begin
            mem_q           <= mem_n;
            read_pointer_q  <= read_pointer_n;
            write_pointer_q <= write_pointer_n;
            status_cnt_q    <= status_cnt_n;
        end
    end

endmodule
