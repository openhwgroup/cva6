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

/* verilator lint_off DECLFILENAME */
module fifo #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter int unsigned THRESHOLD    = 1,    // fill count until when to assert threshold_o
    parameter type dtype                = logic [DATA_WIDTH-1:0]
)(
    input  logic  clk_i,            // Clock
    input  logic  rst_ni,           // Asynchronous reset active low
    input  logic  flush_i,          // flush the queue
    input  logic  testmode_i,       // test_mode to bypass clock gating
    // status flags
    output logic  full_o,           // queue is full
    output logic  empty_o,          // queue is empty
    output logic  threshold_o,      // the FIFO is above the specified threshold
    // as long as the queue is not full we can push new data
    input  dtype  data_i,           // data to push into the queue
    input  logic  push_i,           // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    output dtype  data_o,           // output data
    input  logic  pop_i             // pop head from queue
);
    fifo_v2 #(
        .FALL_THROUGH ( FALL_THROUGH ),
        .DATA_WIDTH   ( DATA_WIDTH   ),
        .DEPTH        ( DEPTH        ),
        .ALM_FULL_TH  ( THRESHOLD    ),
        .dtype        ( dtype        )
    ) impl (
        .clk_i       ( clk_i       ),
        .rst_ni      ( rst_ni      ),
        .flush_i     ( flush_i     ),
        .testmode_i  ( testmode_i  ),
        .full_o      ( full_o      ),
        .empty_o     ( empty_o     ),
        .alm_full_o  ( threshold_o ),
        .alm_empty_o (             ),
        .data_i      ( data_i      ),
        .push_i      ( push_i      ),
        .data_o      ( data_o      ),
        .pop_i       ( pop_i       )
    );
endmodule
/* verilator lint_on DECLFILENAME */
