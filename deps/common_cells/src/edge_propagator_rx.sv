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

module edge_propagator_rx (
    input  logic clk_i,
    input  logic rstn_i,
    input  logic valid_i,
    output logic ack_o,
    output logic valid_o
);

    pulp_sync_wedge i_sync_clkb (
        .clk_i    ( clk_i   ),
        .rstn_i   ( rstn_i  ),
        .en_i     ( 1'b1    ),
        .serial_i ( valid_i ),
        .r_edge_o ( valid_o ),
        .f_edge_o (         ),
        .serial_o ( ack_o   )
    );

endmodule
