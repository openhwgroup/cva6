// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba
// Description: Divides the clock by an integer factor
module clk_div #(
    parameter int unsigned RATIO = 4
)(
    input  logic clk_i,      // Clock
    input  logic rst_ni,     // Asynchronous reset active low
    input  logic testmode_i, // testmode
    input  logic en_i,       // enable clock divider
    output logic clk_o       // divided clock out
);
    logic [RATIO-1:0] counter_q;
    logic clk_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            clk_q       <= 1'b0;
            counter_q <= '0;
        end else begin
            clk_q <= 1'b0;
            if (en_i) begin
                if (counter_q == (RATIO[RATIO-1:0] - 1)) begin
                    clk_q <= 1'b1;
                end else begin
                    counter_q <= counter_q + 1;
                end
            end
        end
    end
    // output assignment - bypass in testmode
    assign clk_o = testmode_i ? clk_i : clk_q;
endmodule
