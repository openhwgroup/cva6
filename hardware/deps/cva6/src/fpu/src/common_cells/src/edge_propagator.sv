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

module edge_propagator (
    input  logic clk_tx_i,
    input  logic rstn_tx_i,
    input  logic edge_i,
    input  logic clk_rx_i,
    input  logic rstn_rx_i,
    output logic edge_o
);

    logic [1:0] sync_a;
    logic       sync_b;

    logic r_input_reg;
    logic s_input_reg_next;

    assign s_input_reg_next = edge_i | (r_input_reg & (~sync_a[0]));

    always @(negedge rstn_tx_i or posedge clk_tx_i) begin
        if (~rstn_tx_i) begin
            r_input_reg <= 1'b0;
            sync_a      <= 2'b00;
        end else begin
            r_input_reg <= s_input_reg_next;
            sync_a      <= {sync_b,sync_a[1]};
        end
    end

    pulp_sync_wedge i_sync_clkb (
        .clk_i    ( clk_rx_i     ),
        .rstn_i   ( rstn_rx_i    ),
        .en_i     ( 1'b1         ),
        .serial_i ( r_input_reg  ),
        .r_edge_o ( edge_o       ),
        .f_edge_o (              ),
        .serial_o ( sync_b       )
    );

endmodule
