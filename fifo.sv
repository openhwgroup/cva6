// Author: Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: Generic FIFO implementation
//
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
module fifo #(
        parameter type dtype            = logic[63:0],
        parameter int unsigned DEPTH    = 4
    )(
        input  logic clk_i,    // Clock
        input  logic rst_ni,   // Asynchronous reset active low
        input  logic flush_i,  // flush the queue
        // status flags
        output logic full_o,   // queue is full
        output logic empty_o,  // queue is empty
        output logic single_element_o, // there is just a single element in the queue
        // as long as the queue is not full we can push new data
        input  dtype data_i,  // data to push into the queue
        input  logic push_i,  // data is valid and can be pushed to the queue
        // as long as the queue is not empty we can pop new elements
        output dtype data_o,  // output data
        input  logic pop_i    // pop head from queue
    );
    // pointer to the read and write section of the queue
    logic [$clog2(DEPTH) - 1:0] read_pointer_n, read_pointer_q, write_pointer_n, write_pointer_q;
    // keep a counter to keep track of the current queue status
    int unsigned status_cnt_n, status_cnt_q; // this integer will be truncated by the synthesis tool
    // actual memory
    dtype [DEPTH-1:0] mem_n, mem_q;

    assign full_o            = (status_cnt_q == DEPTH-1);
    assign empty_o           = (status_cnt_q == 0);
    assign single_element_o = (status_cnt_q == 1);
    // read and write queue logic
    always_comb begin : read_write_comb
        // default assignment
        read_pointer_n  = read_pointer_q;
        write_pointer_n = write_pointer_q;
        status_cnt_n    = status_cnt_q;
        data_o          = mem_q[read_pointer_q];
        mem_n           = mem_q;
        // push a new element to the queue
        if (push_i && ~full_o) begin
            // push the data onto the queue
            mem_n[write_pointer_q] = data_i;
            // increment the write counter, this counter can overflow
            write_pointer_n = write_pointer_q + 1;
            // increment the overall counter
            status_cnt_n    = status_cnt_q + 1;
        end

        if (pop_i && ~empty_o) begin
            // read from the queue is a default assignment
            // but increment the read pointer...
            read_pointer_n = read_pointer_q + 1;
            // ... and decrement the overall count
            status_cnt_n   = status_cnt_q - 1;
        end
        // keep the count pointer stable if we push and pop at the same time
        if (push_i &&  ~full_o && pop_i && ~empty_o)
            status_cnt_n   = status_cnt_q;
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            read_pointer_q  <= '{default: 0};
            write_pointer_q <= '{default: 0};
            status_cnt_q    <= '{default: 0};
            mem_q           <= '{default: 0};
        end else if (flush_i) begin
            read_pointer_q  <= '{default: 0};
            write_pointer_q <= '{default: 0};
            status_cnt_q    <= '{default: 0};
            mem_q           <= '{default: 0};
        end else begin
            read_pointer_q  <= read_pointer_n;
            write_pointer_q <= write_pointer_n;
            status_cnt_q    <= status_cnt_n;
            mem_q           <= mem_n;
        end
    end

    `ifndef SYNTHESIS
    `ifndef verilator
    initial begin
        assert (DEPTH == 2**$clog2(DEPTH)) else $fatal("FIFO size needs to be a power of two.");

    assert property(
        @(posedge clk_i) (rst_ni && full_o |-> ~push_i))
        else $error ("Trying to push new data although the FIFO is full.");

    assert property(
        @(posedge clk_i) (rst_ni && empty_o |-> ~pop_i))
        else $error ("Trying to pop data although the FIFO is empty.");
    end
    `endif
    `endif
endmodule