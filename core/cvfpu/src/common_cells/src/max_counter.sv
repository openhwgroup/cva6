// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Up/down counter that tracks its maximum value

module max_counter #(
    parameter int unsigned WIDTH = 4
) (
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             clear_i,       // synchronous clear for counter
    input  logic             clear_max_i,   // synchronous clear for maximum value
    input  logic             en_i,          // enable the counter
    input  logic             load_i,        // load a new value
    input  logic             down_i,        // downcount, default is up
    input  logic [WIDTH-1:0] delta_i,       // counter delta
    input  logic [WIDTH-1:0] d_i,
    output logic [WIDTH-1:0] q_o,
    output logic [WIDTH-1:0] max_o,
    output logic             overflow_o,
    output logic             overflow_max_o
);
    logic [WIDTH-1:0] max_d, max_q;
    logic overflow_max_d, overflow_max_q;

    delta_counter #(
        .WIDTH           (WIDTH),
        .STICKY_OVERFLOW (1'b1)
    ) i_counter (
        .clk_i,
        .rst_ni,
        .clear_i,
        .en_i,
        .load_i,
        .down_i,
        .delta_i,
        .d_i,
        .q_o,
        .overflow_o
    );

    always_comb begin
        max_d = max_q;
        max_o = max_q;
        overflow_max_d = overflow_max_q;
        if (clear_max_i) begin
            max_d = '0;
            overflow_max_d = 1'b0;
        end else if (q_o > max_q) begin
            max_d = q_o;
            max_o = q_o;
            if (overflow_o) begin
                overflow_max_d = 1'b1;
            end
        end
    end

    assign overflow_max_o = overflow_max_q;

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni) begin
           max_q <= '0;
           overflow_max_q <= 1'b0;
        end else begin
           max_q <= max_d;
           overflow_max_q <= overflow_max_d;
        end
    end

endmodule
