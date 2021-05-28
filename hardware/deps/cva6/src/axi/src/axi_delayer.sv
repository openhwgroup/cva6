// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba, zarubaf@iis.ee.ethz.ch
// Description: Synthesiseable module which (randomly) delays AXI channels

module axi_delayer #(
    parameter type aw_t = logic,
    parameter type w_t  = logic,
    parameter type b_t  = logic,
    parameter type ar_t = logic,
    parameter type r_t  = logic,
    parameter bit StallRandomOutput = 0,
    parameter bit StallRandomInput  = 0,
    parameter int FixedDelayInput   = 1,
    parameter int FixedDelayOutput  = 1
) (
    input  logic clk_i,   // Clock
    input  logic rst_ni,  // Asynchronous reset active low
    // input side
    input  logic aw_valid_i,
    input  aw_t  aw_chan_i,
    output logic aw_ready_o,

    input  logic w_valid_i,
    input  w_t   w_chan_i,
    output logic w_ready_o,

    output logic b_valid_o,
    output b_t   b_chan_o,
    input  logic b_ready_i,

    input  logic ar_valid_i,
    input  ar_t  ar_chan_i,
    output logic ar_ready_o,

    output logic r_valid_o,
    output r_t   r_chan_o,
    input  logic r_ready_i,

    // output side
    output logic aw_valid_o,
    output aw_t  aw_chan_o,
    input  logic aw_ready_i,

    output logic w_valid_o,
    output w_t   w_chan_o,
    input  logic w_ready_i,

    input  logic b_valid_i,
    input  b_t   b_chan_i,
    output logic b_ready_o,

    output logic ar_valid_o,
    output ar_t  ar_chan_o,
    input  logic ar_ready_i,

    input  logic r_valid_i,
    input  r_t   r_chan_i,
    output logic r_ready_o
);
    // AW
    stream_delay #(
      .StallRandom ( StallRandomInput ),
      .FixedDelay  ( FixedDelayInput  ),
      .payload_t   ( aw_t             )
    ) i_stream_delay_aw (
      .clk_i     ( clk_i      ),
      .rst_ni    ( rst_ni     ),
      .payload_i ( aw_chan_i  ),
      .ready_o   ( aw_ready_o ),
      .valid_i   ( aw_valid_i ),
      .payload_o ( aw_chan_o  ),
      .ready_i   ( aw_ready_i ),
      .valid_o   ( aw_valid_o )
    );

    // AR
    stream_delay #(
      .StallRandom ( StallRandomInput ),
      .FixedDelay  ( FixedDelayInput  ),
      .payload_t   ( ar_t             )
    ) i_stream_delay_ar (
      .clk_i     ( clk_i      ),
      .rst_ni    ( rst_ni     ),
      .payload_i ( ar_chan_i  ),
      .ready_o   ( ar_ready_o ),
      .valid_i   ( ar_valid_i ),
      .payload_o ( ar_chan_o  ),
      .ready_i   ( ar_ready_i ),
      .valid_o   ( ar_valid_o )
    );

    // W
    stream_delay #(
      .StallRandom ( StallRandomInput ),
      .FixedDelay  ( FixedDelayInput  ),
      .payload_t   ( w_t              )
    ) i_stream_delay_w (
      .clk_i     ( clk_i      ),
      .rst_ni    ( rst_ni     ),
      .payload_i ( w_chan_i   ),
      .ready_o   ( w_ready_o  ),
      .valid_i   ( w_valid_i  ),
      .payload_o ( w_chan_o   ),
      .ready_i   ( w_ready_i  ),
      .valid_o   ( w_valid_o  )
    );

    // B
    stream_delay #(
      .StallRandom ( StallRandomOutput ),
      .FixedDelay  ( FixedDelayOutput  ),
      .payload_t   ( b_t               )
    ) i_stream_delay_b (
      .clk_i     ( clk_i      ),
      .rst_ni    ( rst_ni     ),
      .payload_i ( b_chan_i   ),
      .ready_o   ( b_ready_o  ),
      .valid_i   ( b_valid_i  ),
      .payload_o ( b_chan_o   ),
      .ready_i   ( b_ready_i  ),
      .valid_o   ( b_valid_o  )
    );

    // R
     stream_delay #(
      .StallRandom ( StallRandomOutput ),
      .FixedDelay  ( FixedDelayOutput  ),
      .payload_t   ( r_t               )
    ) i_stream_delay_r (
      .clk_i     ( clk_i      ),
      .rst_ni    ( rst_ni     ),
      .payload_i ( r_chan_i   ),
      .ready_o   ( r_ready_o  ),
      .valid_i   ( r_valid_i  ),
      .payload_o ( r_chan_o   ),
      .ready_i   ( r_ready_i  ),
      .valid_o   ( r_valid_o  )
    );

endmodule
