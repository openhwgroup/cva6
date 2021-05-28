// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Antonio Pullini <pullinia@iis.ee.ethz.ch>

module edge_propagator_tx (
    input  logic clk_i,
    input  logic rstn_i,
    input  logic valid_i,
    input  logic ack_i,
    output logic valid_o
);

    logic [1:0]   sync_a;

    logic    r_input_reg;
    logic    s_input_reg_next;

    assign s_input_reg_next = valid_i | (r_input_reg & ~sync_a[0]);

    always @(negedge rstn_i or posedge clk_i) begin
        if (~rstn_i) begin
            r_input_reg <= 1'b0;
            sync_a      <= 2'b00;
        end else begin
            r_input_reg <= s_input_reg_next;
            sync_a      <= {ack_i,sync_a[1]};
        end
    end

    assign valid_o = r_input_reg;

endmodule
