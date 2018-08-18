// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

module fifo #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter int unsigned ALM_EMPTY_TH = 1,    // almost empty threshold (when to assert alm_empty_o)
    parameter int unsigned ALM_FULL_TH  = 1,    // almost full threshold (when to assert alm_full_o)
    parameter type dtype                = logic [DATA_WIDTH-1:0]
)(
    input  logic  clk_i,            // Clock
    input  logic  rst_ni,           // Asynchronous reset active low
    input  logic  flush_i,          // flush the queue
    input  logic  testmode_i,       // test_mode to bypass clock gating
    // status flags
    output logic  full_o,           // queue is full
    output logic  empty_o,          // queue is empty
    output logic  alm_full_o,       // FIFO fillstate >= the specified threshold
    output logic  alm_empty_o,      // FIFO fillstate <= the specified threshold
    // as long as the queue is not full we can push new data
    input  dtype  data_i,           // data to push into the queue
    input  logic  push_i,           // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    output dtype  data_o,           // output data
    input  logic  pop_i             // pop head from queue
);
    // local parameter
    // FIFO depth - handle the case of pass-through, synthesizer will do constant propagation
    localparam int unsigned FIFO_DEPTH = (DEPTH > 0) ? DEPTH : 1;
    localparam int unsigned ADDR_DEPTH = (DEPTH > 1) ? $clog2(DEPTH) : 1;
    // clock gating control
    logic gate_clock;
    // pointer to the read and write section of the queue
    logic [ADDR_DEPTH - 1:0] read_pointer_n, read_pointer_q, write_pointer_n, write_pointer_q;
    // keep a counter to keep track of the current queue status
    logic [ADDR_DEPTH:0] status_cnt_n, status_cnt_q; // this integer will be truncated by the synthesis tool
    // actual memory
    dtype [FIFO_DEPTH - 1:0] mem_n, mem_q;

    if (DEPTH == 0) begin
        assign empty_o     = ~push_i;
        assign full_o      = ~pop_i;
        assign alm_full_o  = 1'b0; // that signal does not make any sense in a FIFO of depth 0
        assign alm_empty_o = 1'b0; // that signal does not make any sense in a FIFO of depth 0
    end else begin
        assign full_o       = (status_cnt_q == FIFO_DEPTH);
        assign empty_o      = (status_cnt_q == 0) & ~(FALL_THROUGH & push_i);
        assign alm_full_o   = (status_cnt_q >= ALM_FULL_TH);
        assign alm_empty_o  = (status_cnt_q <= ALM_EMPTY_TH);
    end
    // status flags

    // read and write queue logic
    always_comb begin : read_write_comb
        // default assignment
        read_pointer_n  = read_pointer_q;
        write_pointer_n = write_pointer_q;
        status_cnt_n    = status_cnt_q;
        data_o          = (DEPTH == 0) ? data_i : mem_q[read_pointer_q];
        mem_n           = mem_q;
        gate_clock      = 1'b1;

        // push a new element to the queue
        if (push_i && ~full_o) begin
            // push the data onto the queue
            mem_n[write_pointer_q] = data_i;
            // un-gate the clock, we want to write something
            gate_clock = 1'b0;
            // increment the write counter
            if (write_pointer_q == FIFO_DEPTH-1)
                write_pointer_n = '0;
            else
                write_pointer_n = write_pointer_q + 1;
            // increment the overall counter
            status_cnt_n    = status_cnt_q + 1;
        end

        if (pop_i && ~empty_o) begin
            // read from the queue is a default assignment
            // but increment the read pointer...
            if (read_pointer_n == FIFO_DEPTH-1)
                read_pointer_n = '0;
            else
                read_pointer_n = read_pointer_q + 1;
            // ... and decrement the overall count
            status_cnt_n   = status_cnt_q - 1;
        end

        // keep the count pointer stable if we push and pop at the same time
        if (push_i && pop_i &&  ~full_o && ~empty_o)
            status_cnt_n   = status_cnt_q;

        // FIFO is in pass through mode -> do not change the pointers
        if (FALL_THROUGH && (status_cnt_q == 0) && push_i && pop_i) begin
            data_o = data_i;
            status_cnt_n = status_cnt_q;
            read_pointer_n = read_pointer_q;
            write_pointer_n = write_pointer_q;
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            read_pointer_q  <= '0;
            write_pointer_q <= '0;
            status_cnt_q    <= '0;
        end else begin
            if (flush_i) begin
                read_pointer_q  <= '0;
                write_pointer_q <= '0;
                status_cnt_q    <= '0;
             end else begin
                read_pointer_q  <= read_pointer_n;
                write_pointer_q <= write_pointer_n;
                status_cnt_q    <= status_cnt_n;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            mem_q <= '0;
        end else if (!gate_clock) begin
            mem_q <= mem_n;
        end
    end
    `ifndef SYNTHESIS
    `ifndef verilator
    initial begin
        // assert ((THRESHOLD - 1) > DEPTH) else $error("Threshold can't be bigger than the DEPTH.");

        assert property(
            @(posedge clk_i) (rst_ni && full_o |-> ~push_i))
            else $warning ("Trying to push new data although the FIFO is full.");

        assert property(
            @(posedge clk_i) (rst_ni && empty_o |-> ~pop_i))
            else $warning ("Trying to pop data although the FIFO is empty.");
    end
    `endif
    `endif
endmodule // generic_fifo
