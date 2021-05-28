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

module counter_properties #(
    parameter int unsigned WIDTH = 4,
    parameter bit STICKY_OVERFLOW = 1'b0
)(
    input logic             clk_i,
    input logic             rst_ni,
    input logic             clear_i, // synchronous clear
    input logic             en_i, // enable the counter
    input logic             load_i, // load a new value
    input logic             down_i, // downcount, default is up
    input logic [WIDTH-1:0] d_i,
    input logic [WIDTH-1:0] q_o,
    input logic             overflow_o
);

    logic resetting;
    logic count_up;
    logic count_down;

    // very first clock indicator
    logic init = 1'b0;
    always_ff @(posedge clk_i) init <= 1'b1;

    // make sure that we touch the reset but otherwise we don't constrain it in
    // any way
    assume property (@(posedge clk_i) (!init) |-> !rst_ni);

    // if we are not regulary using the counter
    assign resetting = (clear_i || load_i);

    // direction
    assign count_up = en_i && !down_i;
    assign count_down = en_i && down_i;

    // test if we can count up
    assert property (@(posedge clk_i)
        disable iff (!rst_ni)
        (count_up && !resetting) |=> q_o == $past(q_o) + {{WIDTH-1{1'b0}}, 1'b1});

    // and count down
    assert property (@(posedge clk_i)
        disable iff (!rst_ni)
        (count_down && !resetting) |=> q_o == $past(q_o) - {{WIDTH-1{1'b0}}, 1'b1});

    // can we clear the counter synchronously
    assert property (@(posedge clk_i)
        disable iff (!rst_ni)
        clear_i |=> q_o == '0);

    // does loading work, considering that clearing has priority
    assert property (@(posedge clk_i)
        disable iff (!rst_ni)
        (load_i && !clear_i) |=> q_o == $past(d_i));

    // do we set overflow flags correctly
    // if we count up and overflow do we set it?
    assert property (@(posedge clk_i)
        disable iff (!rst_ni)
        (($past(q_o) > q_o) && $past(count_up) && $past(!resetting) && $past(!overflow_o))
        |-> (overflow_o));
    assert property (@(posedge clk_i)
        disable iff (!rst_ni)
        (($past(q_o) < q_o) && $past(count_down) && $past(!resetting) && $past(!overflow_o))
        |-> (overflow_o));

    // in sticky mode the overflow flag can only be cleared with a clear or load
    if (STICKY_OVERFLOW == 1'b1) begin
        assert property(@(posedge clk_i)
            disable iff (!rst_ni)
            (overflow_o && !resetting |=> overflow_o));
    end

    // cover sequence should touch interesting cases
    cover property (@(posedge clk_i)
        overflow_o == 1'b1);
    cover property (@(posedge clk_i)
        clear_i == 1'b1);
    cover property (@(posedge clk_i)
        load_i == 1'b1);

endmodule // counter_properties

// propagate parameters from counter to properties
bind counter counter_properties #(
    .WIDTH(WIDTH), .STICKY_OVERFLOW(STICKY_OVERFLOW)
) i_counter_properties(.*);
