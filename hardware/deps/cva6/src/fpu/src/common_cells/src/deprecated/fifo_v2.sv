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

module fifo_v2 #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter int unsigned ALM_EMPTY_TH = 1,    // almost empty threshold (when to assert alm_empty_o)
    parameter int unsigned ALM_FULL_TH  = 1,    // almost full threshold (when to assert alm_full_o)
    parameter type dtype                = logic [DATA_WIDTH-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
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

    logic [ADDR_DEPTH-1:0] usage;

    // generate threshold parameters
    if (DEPTH == 0) begin
        assign alm_full_o  = 1'b0; // that signal does not make any sense in a FIFO of depth 0
        assign alm_empty_o = 1'b0; // that signal does not make any sense in a FIFO of depth 0
    end else begin
        assign alm_full_o   = (usage >= ALM_FULL_TH[ADDR_DEPTH-1:0]);
        assign alm_empty_o  = (usage <= ALM_EMPTY_TH[ADDR_DEPTH-1:0]);
    end

    fifo_v3 #(
        .FALL_THROUGH ( FALL_THROUGH ),
        .DATA_WIDTH   ( DATA_WIDTH   ),
        .DEPTH        ( DEPTH        ),
        .dtype        ( dtype        )
    ) i_fifo_v3 (
        .clk_i,
        .rst_ni,
        .flush_i,
        .testmode_i,
        .full_o,
        .empty_o,
        .usage_o (usage),
        .data_i,
        .push_i,
        .data_o,
        .pop_i
    );

    // pragma translate_off
    `ifndef VERILATOR
        initial begin
            assert (ALM_FULL_TH <= DEPTH)  else $error("ALM_FULL_TH can't be larger than the DEPTH.");
            assert (ALM_EMPTY_TH <= DEPTH) else $error("ALM_EMPTY_TH can't be larger than the DEPTH.");
        end
    `endif
    // pragma translate_on

endmodule // fifo_v2
