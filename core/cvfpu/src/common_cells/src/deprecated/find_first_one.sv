// Copyright 2018 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Deprecated, use lzc unit instead.

/// A leading-one finder / leading zero counter.
/// Set FLIP to 0 for find_first_one => first_one_o is the index of the first one (from the LSB)
/// Set FLIP to 1 for leading zero counter => first_one_o is the number of leading zeroes (from the MSB)
module find_first_one #(
    /// The width of the input vector.
    parameter int WIDTH = -1,
    parameter int FLIP = 0
)(
    input  logic [WIDTH-1:0]         in_i,
    output logic [$clog2(WIDTH)-1:0] first_one_o,
    output logic                     no_ones_o
);

    localparam int NUM_LEVELS = $clog2(WIDTH);

    // pragma translate_off
    initial begin
        assert(WIDTH >= 0);
    end
    // pragma translate_on

    logic [WIDTH-1:0][NUM_LEVELS-1:0]          index_lut;
    logic [2**NUM_LEVELS-1:0]                  sel_nodes;
    logic [2**NUM_LEVELS-1:0][NUM_LEVELS-1:0]  index_nodes;

    logic [WIDTH-1:0] in_tmp;

    for (genvar i = 0; i < WIDTH; i++) begin
        assign in_tmp[i] = FLIP ? in_i[WIDTH-1-i] : in_i[i];
    end

    for (genvar j = 0; j < WIDTH; j++) begin
        assign index_lut[j] = j;
    end

    for (genvar level = 0; level < NUM_LEVELS; level++) begin

        if (level < NUM_LEVELS-1) begin
            for (genvar l = 0; l < 2**level; l++) begin
                assign sel_nodes[2**level-1+l]   = sel_nodes[2**(level+1)-1+l*2] | sel_nodes[2**(level+1)-1+l*2+1];
                assign index_nodes[2**level-1+l] = (sel_nodes[2**(level+1)-1+l*2] == 1'b1) ?
                    index_nodes[2**(level+1)-1+l*2] : index_nodes[2**(level+1)-1+l*2+1];
            end
        end

        if (level == NUM_LEVELS-1) begin
            for (genvar k = 0; k < 2**level; k++) begin
                // if two successive indices are still in the vector...
                if (k * 2 < WIDTH-1) begin
                    assign sel_nodes[2**level-1+k]   = in_tmp[k*2] | in_tmp[k*2+1];
                    assign index_nodes[2**level-1+k] = (in_tmp[k*2] == 1'b1) ? index_lut[k*2] : index_lut[k*2+1];
                end
                // if only the first index is still in the vector...
                if (k * 2 == WIDTH-1) begin
                    assign sel_nodes[2**level-1+k]   = in_tmp[k*2];
                    assign index_nodes[2**level-1+k] = index_lut[k*2];
                end
                // if index is out of range
                if (k * 2 > WIDTH-1) begin
                    assign sel_nodes[2**level-1+k]   = 1'b0;
                    assign index_nodes[2**level-1+k] = '0;
                end
            end
        end
    end

    assign first_one_o = NUM_LEVELS > 0 ? index_nodes[0] : '0;
    assign no_ones_o   = NUM_LEVELS > 0 ? ~sel_nodes[0]  : '1;

endmodule
