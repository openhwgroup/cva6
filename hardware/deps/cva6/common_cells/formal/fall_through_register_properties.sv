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

module fall_through_register_properties #(
    parameter type T = logic  // Vivado requires a default value for type parameters.
)(
    input  logic    clk_i,          // Clock
    input  logic    rst_ni,         // Asynchronous active-low reset
    input  logic    clr_i,          // Synchronous clear
    input  logic    testmode_i,     // Test mode to bypass clock gating
    // Input port
    input  logic    valid_i,
    input  logic    ready_o,
    input  T        data_i,
    // Output port
    input  logic    valid_o,
    input  logic    ready_i,
    input  T        data_o
);
    int    stalls = 0;
    // very first clock indicator
    logic init = 1'b0;
    always_ff @(posedge clk_i) init <= 1'b1;

    // make sure that we touch the reset but otherwise we don't constrain it in
    // any way
    assume property (@(posedge clk_i) (!init) |-> !rst_ni);

    // TODO: relax this constraint
    assume property (@(posedge clk_i) clr_i == 1'b0);

    // assume valid/ready handshake as input
    assume property (@(posedge clk_i)
        disable iff (!rst_ni)
        (valid_i && !ready_o |=> valid_i && $stable(data_i))); // data stability

    // assert valid/ready handshake at output
    assert property (@(posedge clk_i)
        disable iff (!rst_ni)
        (valid_o && !ready_i |=> valid_o && $stable(data_o))); // data stability

    // test combinatorial forwarding
    assert property (@(posedge clk_i)
        disable iff (!rst_ni)
        ((valid_i && ready_o) && ready_i |-> valid_o && (data_i == data_o)));

    // count stalls
    always_ff @(posedge clk_i or negedge rst_ni) begin
        // reset stall on rst, no transaction happening or transaction accepted
        if (!rst_ni || !valid_i || ready_o) begin
            stalls <= 0;
        end else if (valid_i && !ready_o) begin
            stalls <= stalls + 1;
        end
    end
    // we want the input to appear at the output at within 2 cycles
    // TODO: for that we would have to constrain ready_i too, does that even make sense?
    // assert property(@(posedge clk_i)
    //     disable iff (!rst_ni) (stalls < 4));

    // we want to make sure we can handle transactions
    cover property (@(posedge clk_i)
        (valid_i && ready_o));
    cover property (@(posedge clk_i)
        (valid_o && ready_i));
    // stall for a bit
    cover property (@(posedge clk_i)
        !ready_i ##5 ready_i);
    cover property (@(posedge clk_i)
        stalls > 10);

endmodule // counter_properties

// propagate parameters from counter to properties
bind fall_through_register fall_through_register_properties #(
    .T(T)
) i_fall_through_register_properties(.*);
