// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Robert Balas <balasr@iis.ee.ethz.ch>

module fifo_v3_properties #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter type dtype                = logic [DATA_WIDTH-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
) (
    input logic                    clk_i, // Clock
    input logic                    rst_ni, // Asynchronous reset active low
    input logic                    flush_i, // flush the queue
    input logic                    testmode_i, // test_mode to bypass clock gating
    // status flags
    input logic                    full_o, // queue is full
    input logic                    empty_o, // queue is empty
    input logic [ADDR_DEPTH-1:0]   usage_o, // fill pointer
    // as long as the queue is not full we can push new data
    input logic                    push_i, // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    input logic                    pop_i, // pop head from queue

    input logic [ADDR_DEPTH - 1:0] read_pointer_n,
    input logic [ADDR_DEPTH - 1:0] read_pointer_q,
    input logic [ADDR_DEPTH - 1:0] write_pointer_n,
    input logic [ADDR_DEPTH - 1:0] write_pointer_q,

    input logic [ADDR_DEPTH:0]     status_cnt_n, // counter to keep track of the current queue status
    input logic [ADDR_DEPTH:0]     status_cnt_q
);

    localparam int unsigned FIFO_DEPTH = (DEPTH > 0) ? DEPTH : 1;
    // verbatim from fifo_v3
    localparam int unsigned FIFO_SIZE  = FIFO_DEPTH[ADDR_DEPTH:0];

    logic [ADDR_DEPTH-1:0] fill_level;
    logic                  read_incr;
    logic                  write_incr;
    int                    writes = 0; // number of writes to fifo
    int                    reads  = 0; // number of reads from fifo

    // We use this as a workaround to trigger and initial event at the beginning
    // of the simulation. I can't think of a better way with the subset of sv
    // yosys supports.
    logic init = 1'b0;
    always_ff @(posedge clk_i) init <= 1'b1;

    // make sure that we touch the reset but otherwise we don't constrain it in
    // any way
    assume property (@(posedge clk_i) (!init) |-> !rst_ni);

    // we don't have tests for FALL_THROUGH mode
    always_comb assert (FALL_THROUGH == 1'b0);

    // assume we are good boys and dont try to mess with the queue
    // It doesn't look like we need these assumptions
    // assume property(@(posedge clk_i)
    //     disable iff (!rst_ni) (full_o |-> !push_i));

    // assume property(@(posedge clk_i)
    //     disable iff (!rst_ni) (empty_o |-> !pop_i));


    assign fill_level = writes - reads;
    assign read_incr = read_pointer_n - read_pointer_q;
    assign write_incr = write_pointer_n - write_pointer_q;

    // writes and reads track the number of writes and reads to the fifo. Our
    // assumption and assertions make sure that these values stay logically
    // consistent.
    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni) begin
            writes <= 0;
            reads  <= 0;
        end else begin
            if (flush_i) begin
                writes <= 0;
                reads  <= 0;
            end else begin
                writes <= writes + write_incr;
                reads  <= reads + read_incr;
            end
        end
    end

    // assume that we test for a finite amount of transactions otherwise the
    // solver tries to be cute by overflowing the writes and reads variables
    assume property (@(posedge clk_i)
        (reads < 1024 && writes < 1024));
    // start induction with correct internal fill level
    assume property (@(posedge clk_i)
        ((writes - reads) == status_cnt_q));

    // don't underflow
    assert property (@(posedge clk_i)
        (writes >= reads));
    // don't overflow
    assert property (@(posedge clk_i)
        ((writes - reads) <= FIFO_SIZE));

    // do we set fill indicators properly
    assert property (@(posedge clk_i)
        ((writes == reads) |-> empty_o));
    assert property (@(posedge clk_i)
        (((writes - reads) == FIFO_SIZE) |-> full_o));
    // check if we compute fill level correctly
    assert property (@(posedge clk_i)
        disable iff (!rst_ni) (fill_level == usage_o));

    // sanity of internal vars
    assert property (@(posedge clk_i)
        status_cnt_q <= FIFO_SIZE);

    // make sure we hit the interesting cases
    cover property (@(posedge clk_i)
        full_o == 1'b1);
    cover property (@(posedge clk_i)
        empty_o == 1'b1);

endmodule // fifo_v3_properties

// propagate parameters from fifo_v3 to properties
bind fifo_v3 fifo_v3_properties #(
    .FALL_THROUGH(FALL_THROUGH), .DATA_WIDTH(DATA_WIDTH), .DEPTH(DEPTH)
) i_fifo_v3_properties(.*);
