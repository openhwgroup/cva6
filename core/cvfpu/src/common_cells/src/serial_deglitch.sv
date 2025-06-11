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
// Description: Deglitches a serial line by taking multiple samples until
//              asserting the output high/low.

module serial_deglitch #(
    parameter int unsigned SIZE = 4
)(
    input  logic clk_i,    // clock
    input  logic rst_ni,   // asynchronous reset active low
    input  logic en_i,     // enable
    input  logic d_i,      // serial data in
    output logic q_o       // filtered data out
);
    logic [SIZE-1:0] count_q;
    logic q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            count_q <= '0;
            q       <= 1'b0;
        end else begin
            if (en_i) begin
                if (d_i == 1'b1 && count_q != SIZE[SIZE-1:0]) begin
                    count_q <= count_q + 1;
                end else if (d_i == 1'b0 && count_q != SIZE[SIZE-1:0]) begin
                    count_q <= count_q - 1;
                end
            end
        end
    end

    // output process
    always_comb begin
        if (count_q == SIZE[SIZE-1:0]) begin
            q_o = 1'b1;
        end else if (count_q == 0) begin
            q_o = 1'b0;
        end
    end
endmodule
